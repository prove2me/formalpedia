-- Prove2me | solution 1 for DSDensity1246.Main.Supplement.optimal_realizable_list_learning
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-19T17:26:48.084957+00:00
-- url     : https://prove2.me/submissions/7ca95f1b-b513-43ec-930f-eac534bb8de5

import Mathlib
import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_Supplement_predictor

section
open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Dev.Learn

open DSDensity1246.Main DSDensity1246.Main.Supplement

/-! A data law with a "partition" sigma-algebra: the sigma-algebra is the comap of `φ : Z → Bool`,
and the measure is a Dirac mass at `z0`. Outer measures of sets are then 1 as soon as the set meets
the atom of `z0`. -/

noncomputable def lawOf {Z : Type} (φ : Z → Bool) (z0 : Z) : DataLaw Z :=
  letI : MeasurableSpace Z := MeasurableSpace.comap φ ⊤
  ⟨this, ⟨Measure.dirac z0, inferInstance⟩⟩

lemma pi_dirac' {Z : Type*} [MeasurableSpace Z] (z0 : Z) (m : ℕ) :
    Measure.pi (fun _ : Fin m => Measure.dirac z0) = Measure.dirac (fun _ : Fin m => z0) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [fun i => Measure.dirac_apply' z0 (hs i)]
  by_cases h : ∀ i, z0 ∈ s i
  · have h' : (fun _ : Fin m => z0) ∈ Set.pi Set.univ s := fun i _ => h i
    simp [Set.indicator_of_mem h', Set.indicator_of_mem (h _)]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have h' : (fun _ : Fin m => z0) ∉ Set.pi Set.univ s := fun hh => hi (hh i trivial)
    rw [Set.indicator_of_notMem h']
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Set.indicator_of_notMem hi])

lemma lb {Z R : Type*} [MeasurableSpace Z] [MeasurableSpace R] (z0 : Z) (ρ : Measure R)
    [SFinite ρ] (m : ℕ) (F : Set ((Fin m → Z) × R)) :
    ρ {u | ((fun _ : Fin m => z0), u) ∈ F} ≤
      ((Measure.pi fun _ : Fin m => Measure.dirac z0).prod ρ) F := by
  rw [pi_dirac']
  rw [← measure_toMeasurable F]
  have hM := measurableSet_toMeasurable ((Measure.dirac (fun _ : Fin m => z0)).prod ρ) F
  rw [Measure.prod_apply hM, lintegral_dirac' _ (measurable_measure_prodMk_left hM)]
  exact measure_mono (fun u hu => subset_toMeasurable _ F hu)

lemma outer_one {Z : Type} (φ : Z → Bool) (z0 : Z) (A : Set Z) (z' : Z) (hz' : z' ∈ A)
    (hφ : φ z' = φ z0) :
    ((lawOf φ z0).2 : @Measure Z (lawOf φ z0).1) A = 1 := by
  letI : MeasurableSpace Z := MeasurableSpace.comap φ ⊤
  show Measure.dirac z0 A = 1
  rw [← measure_toMeasurable A]
  have hM : MeasurableSet (toMeasurable (Measure.dirac z0) A) := measurableSet_toMeasurable _ _
  obtain ⟨T, -, hT⟩ := (MeasurableSpace.measurableSet_comap).1 hM
  apply Measure.dirac_apply_of_mem
  have h1 : z' ∈ toMeasurable (Measure.dirac z0) A := subset_toMeasurable _ _ hz'
  rw [← hT] at h1 ⊢
  simp only [Set.mem_preimage] at h1 ⊢
  rwa [← hφ]

lemma lawOf_error {X Y : Type} {ℓ : ℕ} (φ : X × Y → Bool) (z0 : X × Y) (μ : ListPredictor X Y ℓ)
    (z' : X × Y) (hz' : z'.2 ∉ (μ z'.1).1) (hφ : φ z' = φ z0) :
    listError (lawOf φ z0) μ = 1 :=
  outer_one φ z0 _ z' hz' hφ

lemma lawOf_realizable {X Y : Type} (φ : X × Y → Bool) (z0 : X × Y) (H : Set (X → Y))
    (h : X → Y) (hh : h ∈ H) (hm : MeasurableSet[MeasurableSpace.comap φ ⊤] {z : X × Y | h z.1 ≠ z.2})
    (hz : h z0.1 = z0.2) : Realizable (lawOf φ z0) H := by
  letI : MeasurableSpace (X × Y) := MeasurableSpace.comap φ ⊤
  unfold Realizable bestError
  apply le_antisymm _ bot_le
  refine (iInf_le _ ⟨h, hh⟩).trans ?_
  show Measure.dirac z0 _ ≤ 0
  rw [Measure.dirac_apply' _ hm]
  simp [hz]


/-! The class `{const false, id}` on `Bool`. -/

def Hs : Set (Bool → Bool) := {fun _ => false, id}

open scoped Classical in
lemma Hs_dim : listDSDim 1 Hs = 1 := by
  apply le_antisymm
  · refine iSup₂_le fun d S => iSup_le fun hS => ?_
    by_contra hlt
    have h2 : 2 ≤ d := by
      have : (1 : ℕ∞) < d := not_le.1 hlt
      exact_mod_cast this
    obtain ⟨F, hFsub, hne, hnb⟩ := hS
    obtain ⟨f, hf⟩ := hne
    let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    have hmem : ∀ g ∈ F, g = (fun _ => false) ∘ S ∨ g = id ∘ S := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := hFsub hg
      rcases hh with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have n0 := hnb f hf i0
    have n1 := hnb f hf i1
    obtain ⟨g, hg⟩ := Finset.card_pos.1 (by omega : 0 < (F.filter (fun g => DirectionalNeighbor i0 f g)).card)
    obtain ⟨g', hg'⟩ := Finset.card_pos.1 (by omega : 0 < (F.filter (fun g => DirectionalNeighbor i1 f g)).card)
    rw [Finset.mem_filter] at hg hg'
    obtain ⟨hgF, hgn⟩ := hg
    obtain ⟨hgF', hgn'⟩ := hg'
    have h01 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
    have h10 : i0 ≠ i1 := h01.symm
    have e1 : f i0 ≠ g i0 := hgn.1
    have e2 : f i1 ≠ g' i1 := hgn'.1
    have e3 : g i1 = f i1 := (hgn.2 i1 h01).symm
    rcases hmem f hf with rfl | rfl <;> rcases hmem g hgF with rfl | rfl <;>
      rcases hmem g' hgF' with rfl | rfl <;> simp_all
  · refine le_iSup₂_of_le 1 (fun _ => true) (le_iSup_of_le ?_ le_rfl)
    refine ⟨{fun _ => false, fun _ => true}, ?_, ?_, ?_⟩
    · intro g hg
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨fun _ => false, Or.inl rfl, rfl⟩
      · exact ⟨id, Or.inr rfl, rfl⟩
    · exact ⟨_, Finset.mem_insert_self _ _⟩
    · intro f hf i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      push Not
      rcases hf with rfl | rfl
      · exact ⟨fun _ => true, by simp, by simp [DirectionalNeighbor]⟩
      · exact ⟨fun _ => false, by simp, by simp [DirectionalNeighbor]⟩


def z0 : Bool × Bool := (false, false)

noncomputable def D0 : DataLaw (Bool × Bool) := lawOf (fun z => z.2) z0
noncomputable def DE : DataLaw (Bool × Bool) := lawOf (fun z => decide (z.1 = z.2)) z0

lemma D0_real : Realizable D0 Hs :=
  lawOf_realizable _ _ Hs (fun _ => false) (Or.inl rfl)
    (by
      have : {z : Bool × Bool | (fun _ : Bool => false) z.1 ≠ z.2} =
          (fun z : Bool × Bool => z.2) ⁻¹' {true} := by
        ext z; cases z.2 <;> simp
      rw [this]
      exact ⟨{true}, MeasurableSet.of_discrete, rfl⟩) rfl

lemma DE_real : Realizable DE Hs :=
  lawOf_realizable _ _ Hs id (Or.inr rfl)
    (by
      have : {z : Bool × Bool | id z.1 ≠ z.2} =
          (fun z : Bool × Bool => decide (z.1 = z.2)) ⁻¹' {false} := by
        ext z; simp
      rw [this]
      exact ⟨{false}, MeasurableSet.of_discrete, rfl⟩) rfl

lemma one_of_pred (μ : ListPredictor Bool Bool 1) :
    listError D0 μ = 1 ∨ listError DE μ = 1 := by
  by_cases h1 : false ∈ (μ true).1
  · by_cases h2 : true ∈ (μ true).1
    · exfalso
      have hc := (μ true).2
      have : ({false, true} : Finset Bool) ⊆ (μ true).1 := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl <;> assumption
      have := Finset.card_le_card this
      simp at this
      omega
    · exact Or.inr (lawOf_error _ _ μ (true, true) (by simpa using h2) (by simp [z0]))
  · exact Or.inl (lawOf_error _ _ μ (true, false) (by simpa using h1) (by simp [z0]))

/-- The published statement (specialised to `X = Y = Bool`) is false. -/
theorem chk_optimal_realizable_list_learning_false :
    ¬ (∀ (H : Set (Bool → Bool)) (ℓ d : ℕ) (_ : 1 ≤ ℓ) (_ : listDSDim ℓ H = d),
    ∃ (C : OrientationChoice Bool Bool ℓ H) (ρ : ProbabilityMeasure ℝ),
      (ρ : Measure ℝ) = volume.restrict (Set.Ico (0 : ℝ) 1) ∧
      ∀ (D : DataLaw (Bool × Bool)), Realizable D H →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          ∀ m : ℕ,
            (if d = 0 then 0 else ⌈512 * ((d : ℝ) + Real.log (1 / δ)) / ε⌉₊) ≤ m →
            failureProbability D ρ (validatedLearner d C) ε δ m 0 ≤ ENNReal.ofReal δ) := by
  intro hthm
  obtain ⟨C, ρ, -, h⟩ := hthm Hs 1 1 le_rfl Hs_dim
  have hε0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hε1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hδ0 : (0 : ℝ) < 2 / 5 := by norm_num
  have hδ1 : (2 / 5 : ℝ) < 1 := by norm_num
  set m : ℕ := ⌈512 * (((1 : ℕ) : ℝ) + Real.log (1 / (2 / 5 : ℝ))) / (1 / 2 : ℝ)⌉₊ with hm
  have hmm : (if (1 : ℕ) = 0 then 0 else ⌈512 * (((1 : ℕ) : ℝ) + Real.log (1 / (2 / 5 : ℝ))) / (1 / 2 : ℝ)⌉₊) ≤ m := by
    simp [hm]
  have h0 := h D0 D0_real _ _ hε0 hε1 hδ0 hδ1 m hmm
  have hE := h DE DE_real _ _ hε0 hε1 hδ0 hδ1 m hmm
  let L : ℝ → ListPredictor Bool Bool 1 := fun u =>
    validatedLearner (H := Hs) 1 C (1 / 2) (2 / 5) m (fun _ => z0) u
  let U0 : Set ℝ := {u | (0 : ℝ≥0∞) + ENNReal.ofReal (1 / 2) < listError D0 (L u)}
  let UE : Set ℝ := {u | (0 : ℝ≥0∞) + ENNReal.ofReal (1 / 2) < listError DE (L u)}
  have hhalf : (0 : ℝ≥0∞) + ENNReal.ofReal (1 / 2) < 1 := by
    rw [zero_add]
    exact (ENNReal.ofReal_lt_one).2 hε1
  have hcover : Set.univ ⊆ U0 ∪ UE := by
    intro u _
    rcases one_of_pred (L u) with h1 | h1
    · exact Or.inl (by simp only [U0, Set.mem_setOf_eq]; rw [h1]; exact hhalf)
    · exact Or.inr (by simp only [UE, Set.mem_setOf_eq]; rw [h1]; exact hhalf)
  have hsum : (1 : ℝ≥0∞) ≤ (ρ : Measure ℝ) U0 + (ρ : Measure ℝ) UE := by
    calc (1 : ℝ≥0∞) = (ρ : Measure ℝ) Set.univ := by simp
      _ ≤ (ρ : Measure ℝ) (U0 ∪ UE) := measure_mono hcover
      _ ≤ _ := measure_union_le _ _
  have b0 : (ρ : Measure ℝ) U0 ≤ failureProbability D0 ρ (validatedLearner 1 C) (1 / 2) (2 / 5) m 0 :=
    by
      unfold failureProbability trainingLaw iidLaw
      exact @lb (Bool × Bool) ℝ D0.1 _ z0 (ρ : Measure ℝ) _ m _
  have bE : (ρ : Measure ℝ) UE ≤ failureProbability DE ρ (validatedLearner 1 C) (1 / 2) (2 / 5) m 0 :=
    by
      unfold failureProbability trainingLaw iidLaw
      exact @lb (Bool × Bool) ℝ DE.1 _ z0 (ρ : Measure ℝ) _ m _
  have := hsum.trans (add_le_add (b0.trans h0) (bE.trans hE))
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] at this
  have h45 : ENNReal.ofReal (2 / 5 + 2 / 5) < 1 := (ENNReal.ofReal_lt_one).2 (by norm_num)
  exact absurd this (not_le.2 h45)

end DSDensity1246.Dev.Learn
end

open MeasureTheory DSDensity1246.Main DSDensity1246.Main.Supplement in
theorem solution :
    ¬ (∀ {X Y : Type} (H : Set (X → Y)) (ℓ d : ℕ) (_ : 1 ≤ ℓ) (_ : listDSDim ℓ H = d),
    ∃ (C : OrientationChoice X Y ℓ H) (ρ : ProbabilityMeasure ℝ),
      (ρ : Measure ℝ) = volume.restrict (Set.Ico (0 : ℝ) 1) ∧
      ∀ (D : DataLaw (X × Y)), Realizable D H →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          ∀ m : ℕ,
            (if d = 0 then 0 else ⌈512 * ((d : ℝ) + Real.log (1 / δ)) / ε⌉₊) ≤ m →
            failureProbability D ρ (validatedLearner d C) ε δ m 0 ≤ ENNReal.ofReal δ) := by
  intro h
  exact DSDensity1246.Dev.Learn.chk_optimal_realizable_list_learning_false
    (fun H ℓ d h1 h2 => h H ℓ d h1 h2)
