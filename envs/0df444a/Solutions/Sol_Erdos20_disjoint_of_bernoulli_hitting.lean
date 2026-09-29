-- Prove2me | solution 1 for Erdos20.disjoint_of_bernoulli_hitting
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-09-26T16:18:10.363988+00:00
-- url     : https://prove2.me/submissions/b712c129-fb75-4141-9431-6bcd0b9e7495

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.NormNum


set_option autoImplicit false

open scoped BigOperators

namespace Erdos20

/-- Colors whose color class contains a member of the set family. -/
noncomputable def successfulColors {α : Type*} [DecidableEq α] {q : ℕ}
    (F : Finset (Finset α)) (χ : α → Fin q) : Finset (Fin q) := by
  classical
  exact Finset.univ.filter (fun i => ∃ A ∈ F, ∀ a ∈ A, χ a = i)

@[simp] theorem mem_successfulColors {α : Type*} [DecidableEq α] {q : ℕ}
    (F : Finset (Finset α)) (χ : α → Fin q) (i : Fin q) :
    i ∈ successfulColors F χ ↔ ∃ A ∈ F, ∀ a ∈ A, χ a = i := by
  classical
  simp [successfulColors]

/-- Distinct successful colors yield distinct, disjoint family members.
The nonemptiness assumption prevents the empty set from witnessing many colors. -/
theorem exists_disjoint_of_many_successfulColors {α : Type*} [DecidableEq α]
    {q : ℕ} (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.Nonempty)
    (χ : α → Fin q) (k : ℕ) (hk : k ≤ (successfulColors F χ).card) :
    ∃ H ⊆ F, H.card = k ∧
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by
  classical
  obtain ⟨I, hI, hIcard⟩ := Finset.exists_subset_card_eq hk
  have hw : ∀ i : I, ∃ A ∈ F, ∀ a ∈ A, χ a = (i : Fin q) := by
    intro i
    exact (mem_successfulColors F χ i).mp (hI i.property)
  choose A hAF hAmono using hw
  have hAinj : Function.Injective A := by
    intro i j hij
    obtain ⟨a, ha⟩ := hF (A i) (hAF i)
    apply Subtype.ext
    exact (hAmono i a ha).symm.trans (hAmono j a (hij ▸ ha))
  refine ⟨Finset.univ.image A, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact hAF i
  · rw [Finset.card_image_of_injective _ hAinj]
    simpa using hIcard
  · intro B hB C hC hBC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have hij : i = j := Subtype.ext ((hAmono i a hai).symm.trans (hAmono j a haj))
    exact hBC (congrArg A hij)

/-- Double counting successful color-coloring incidences. -/
theorem sum_successfulColors_card {α : Type*} [Fintype α] [DecidableEq α]
    {q : ℕ} (F : Finset (Finset α)) :
    ∑ i : Fin q, (Finset.univ.filter
        (fun χ : α → Fin q => i ∈ successfulColors F χ)).card =
      ∑ χ : α → Fin q, (successfulColors F χ).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  simp only [successfulColors, Finset.sum_filter]
  congr 1
  ext i
  simp

/-- If every color is successful for at least half of all colorings, some
coloring has at least half its colors successful. -/
theorem exists_coloring_many_successfulColors {α : Type*}
    [Fintype α] [DecidableEq α] (F : Finset (Finset α))
    (k : ℕ) (hk : 0 < k)
    (hhalf : ∀ i : Fin (2 * k), Fintype.card (α → Fin (2 * k)) ≤
      2 * (Finset.univ.filter
        (fun χ : α → Fin (2 * k) => i ∈ successfulColors F χ)).card) :
    ∃ χ : α → Fin (2 * k), k ≤ (successfulColors F χ).card := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hhalf i)
  rw [← Finset.mul_sum, sum_successfulColors_card] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hmean : ∑ _χ : α → Fin (2 * k), k ≤
      ∑ χ : α → Fin (2 * k), (successfulColors F χ).card := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith [hsum]
  have hnonempty : (Finset.univ : Finset (α → Fin (2 * k))).Nonempty := by
    exact ⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨χ, _, hχ⟩ := Finset.exists_le_of_sum_le hnonempty hmean
  exact ⟨χ, hχ⟩

/-- The finite counting form of the Bell--Chueluecha--Warnke coloring step.
The input is a one-color hitting estimate. No independence between different
color classes is required. -/
theorem exists_disjoint_of_half_colorings {α : Type*}
    [Fintype α] [DecidableEq α] (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A.Nonempty) (k : ℕ) (hk : 0 < k)
    (hhalf : ∀ i : Fin (2 * k), Fintype.card (α → Fin (2 * k)) ≤
      2 * (Finset.univ.filter
        (fun χ : α → Fin (2 * k) => i ∈ successfulColors F χ)).card) :
    ∃ H ⊆ F, H.card = k ∧
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by
  obtain ⟨χ, hχ⟩ := exists_coloring_many_successfulColors F k hk hhalf
  exact exists_disjoint_of_many_successfulColors F hF χ k hχ

/-- An equivalent interface using only standard finite-set notation, suitable
for publication without a separate `successfulColors` definition. -/
theorem disjoint_of_half_monochromatic_colorings {α : Type*}
    [Fintype α] [DecidableEq α] (F : Finset (Finset α))
    (hF : ∀ A ∈ F, A.Nonempty) (k : ℕ) (hk : 0 < k)
    (hhalf : ∀ i : Fin (2 * k), Fintype.card (α → Fin (2 * k)) ≤
      2 * (Finset.univ.filter
        (fun χ : α → Fin (2 * k) => ∃ A ∈ F, ∀ a ∈ A, χ a = i)).card) :
    ∃ H ⊆ F, H.card = k ∧
      ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by
  apply exists_disjoint_of_half_colorings F hF k hk
  intro i
  simpa only [mem_successfulColors] using hhalf i

end Erdos20

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Erdos20

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Independent uniform coordinates give the uniform law on all finite colorings. -/
theorem infinitePi_uniform_eq_uniform :
    Measure.infinitePi (fun _ : α => (PMF.uniformOfFintype β).toMeasure) =
      (PMF.uniformOfFintype (α → β)).toMeasure := by
  apply Measure.ext_of_singleton
  intro χ
  rw [Measure.infinitePi_singleton_of_fintype,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- Testing equality with a fixed uniformly chosen color is Bernoulli. -/
theorem uniform_color_indicator_law (i : β) (p : unitInterval)
    (hp : (p : ℝ) = (Fintype.card β : ℝ)⁻¹) :
    (PMF.uniformOfFintype β).toMeasure.map (fun j => j = i) =
      unitInterval.toNNReal p • Measure.dirac True +
        unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  classical
  have hpoint : (PMF.uniformOfFintype β).toMeasure.real {i} = (p : ℝ) := by
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
    simp [hp]
  apply Measure.ext_of_measureReal_singleton
  intro b
  by_cases hb : b
  · rw [show b = True by simp [hb]]
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _) (by simp)]
    simpa [measureReal_def] using hpoint
  · rw [show b = False by simp [hb]]
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _) (by simp)]
    have hpre : (fun j : β => j = i) ⁻¹' {False} = ({i} : Set β)ᶜ := by
      ext j
      simp
    rw [hpre]
    have hcompl : (PMF.uniformOfFintype β).toMeasure.real ({i} : Set β)ᶜ = 1 - (p : ℝ) := by
      rw [measureReal_compl (by simp), hpoint]
      simp
    simpa [measureReal_def] using hcompl

/-- A fixed class of an independent uniform coloring is a Bernoulli random subset. -/
theorem uniform_colorClass_hasLaw (i : β) (p : unitInterval)
    (hp : (p : ℝ) = (Fintype.card β : ℝ)⁻¹) :
    HasLaw (fun χ : α → β => {a | χ a = i}) (setBernoulli Set.univ p)
      (PMF.uniformOfFintype (α → β)).toMeasure where
  aemeasurable := (measurable_of_countable _).aemeasurable
  map_eq := by
    rw [← infinitePi_uniform_eq_uniform, setBernoulli_eq_map]
    calc
      (Measure.infinitePi (fun _ : α => (PMF.uniformOfFintype β).toMeasure)).map
          (fun χ => {a | χ a = i}) =
        ((Measure.infinitePi (fun _ : α => (PMF.uniformOfFintype β).toMeasure)).map
          (fun χ a => χ a = i)).map (fun f : α → Prop => {a | f a}) := by
            symm
            exact Measure.map_map (measurable_of_countable _) (measurable_of_countable _)
      _ = _ := by
        have hcoords := Measure.infinitePi_map_pi
          (fun _ : α => (PMF.uniformOfFintype β).toMeasure)
          (f := fun _ j => j = i) (fun _ => measurable_of_countable _)
        rw [hcoords]
        congr 2
        funext a
        simpa using uniform_color_indicator_law i p hp

/-- A Bernoulli event of probability at least one half occurs for at least half
of all colorings when tested on a specified color class. -/
theorem half_le_setBernoulli_implies_half_colorings (i : β) (p : unitInterval)
    (hp : (p : ℝ) = (Fintype.card β : ℝ)⁻¹) (E : Set (Set α))
    (hE : (1 / 2 : ℝ) ≤ (setBernoulli Set.univ p).real E) :
    Fintype.card (α → β) ≤
      2 * (Finset.univ.filter (fun χ : α → β => {a | χ a = i} ∈ E)).card := by
  classical
  have he : MeasurableSet E := (Set.to_countable E).measurableSet
  have hprob : (1 / 2 : ℝ) ≤ (PMF.uniformOfFintype (α → β)).toMeasure.real
      {χ | {a | χ a = i} ∈ E} := by
    have heq := (uniform_colorClass_hasLaw (α := α) i p hp).measureReal_eq
      (p := fun W => W ∈ E) he
    rw [heq]
    exact hE
  rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _
    (Set.to_countable _).measurableSet] at hprob
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_subtype, Set.mem_ofPred_eq] at hprob
  have hpos : (0 : ℝ) < Fintype.card (α → β) := Nat.cast_pos.mpr Fintype.card_pos
  have hmul := (le_div_iff₀ hpos).mp hprob
  exact_mod_cast (show (Fintype.card (α → β) : ℝ) ≤
    2 * ((Finset.univ.filter (fun χ : α → β => {a | χ a = i} ∈ E)).card : ℝ) by
      linarith)

/-- The event-to-count bridge specialized to containment of a member of a set family. -/
theorem half_monochromatic_colorings_of_bernoulli (F : Finset (Finset α))
    {q : ℕ} (i : Fin q) (p : unitInterval) (hp : (p : ℝ) = (q : ℝ)⁻¹)
    (hF : (1 / 2 : ℝ) ≤ (setBernoulli (Set.univ : Set α) p).real
      {W | ∃ A ∈ F, (A : Set α) ⊆ W}) :
    Fintype.card (α → Fin q) ≤ 2 * (Finset.univ.filter (fun χ : α → Fin q =>
      ∃ A ∈ F, ∀ a ∈ A, χ a = i)).card := by
  letI : Nonempty (Fin q) := ⟨i⟩
  have h := half_le_setBernoulli_implies_half_colorings i p (by simpa using hp)
    {W | ∃ A ∈ F, (A : Set α) ⊆ W} hF
  simpa only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe] using h

end Erdos20

set_option autoImplicit false

namespace Erdos20

/-- The BCW expectation step: a half-probability hitting estimate at sampling
rate 1/(2k) supplies k disjoint nonempty members. -/
private theorem bernoulli_coloring_proof {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.Nonempty)
    (k : ℕ) (hk : 0 < k) (p : unitInterval)
    (hp : (p : ℝ) = (2 * (k : ℝ))⁻¹)
    (hhit : (1 / 2 : ℝ) ≤
      (ProbabilityTheory.setBernoulli (Set.univ : Set α) p).real
        {W | ∃ A ∈ F, (A : Set α) ⊆ W}) :
    ∃ H ⊆ F, H.card = k ∧ ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by
  apply disjoint_of_half_monochromatic_colorings F hF k hk
  intro i
  exact half_monochromatic_colorings_of_bernoulli F i p (by simpa using hp) hhit

end Erdos20

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.Nonempty)
    (k : ℕ) (hk : 0 < k) (p : unitInterval)
    (hp : (p : ℝ) = (2 * (k : ℝ))⁻¹)
    (hhit : (1 / 2 : ℝ) ≤
      (ProbabilityTheory.setBernoulli (Set.univ : Set α) p).real
        {W | ∃ A ∈ F, (A : Set α) ⊆ W}) :
    ∃ H ⊆ F, H.card = k ∧ ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B :=
  Erdos20.bernoulli_coloring_proof F hF k hk p hp hhit
