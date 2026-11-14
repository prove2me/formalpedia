-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.expect_run_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:05.52513+00:00
-- url     : https://prove2.me/submissions/0898c42c-87dc-40aa-86b1-ce8e67105b63

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_Checkpoints
import Theorems.Thm_ConsistentSubmodular_Checkpoints_Law_expect_pi_apply
import Theorems.Thm_ConsistentSubmodular_Checkpoints_le_benchmark
import Theorems.Thm_ConsistentSubmodular_Checkpoints_value_le_run
import Theorems.Thm_ConsistentSubmodular_Checkpoints_subblock_count

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

namespace Law

variable {Ω : Type*} [Fintype Ω]

theorem expect_mono (μ : Law Ω) {X Y : Ω → ℝ} (h : ∀ ω, μ.weight ω ≠ 0 → X ω ≤ Y ω) :
    μ.expect X ≤ μ.expect Y := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : μ.weight ω = 0
  · simp [hω]
  · exact mul_le_mul_of_nonneg_left (h ω hω) (μ.nonneg ω)

theorem expect_add (μ : Law Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_const (μ : Law Ω) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.sum_one, one_mul]

theorem expect_nonneg (μ : Law Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (h ω)

theorem expect_uniform (h : ℕ) (hh : 0 < h) (X : Fin h → ℝ) :
    (uniform h hh).expect X = (∑ i, X i) / h := by
  simp only [expect, uniform, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Weights of a product law vanish unless every coordinate has positive weight. -/
theorem weight_pi_ne_zero {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (μ : ι → Law X) {x : ι → X} (hx : (pi μ).weight x ≠ 0) (i : ι) :
    (μ i).weight (x i) ≠ 0 := by
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

variable {Y : Type*} [Fintype Y]

theorem expect_prod_mul (μ : Law Ω) (ν : Law Y) (F : Ω → ℝ) (G : Y → ℝ) :
    (μ.prod ν).expect (fun p => F p.1 * G p.2) = μ.expect F * ν.expect G := by
  simp only [expect, prod, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => by ring

theorem weight_prod_ne_zero (μ : Law Ω) (ν : Law Y) {p : Ω × Y}
    (hp : (μ.prod ν).weight p ≠ 0) : μ.weight p.1 ≠ 0 ∧ ν.weight p.2 ≠ 0 := by
  simp only [prod] at hp
  exact ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩

end Law

end ConsistentSubmodular.Checkpoints

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-- The addition-robust guarantee at the checkpoint `c`, against every set of at
most `κ` elements arrived by time `c + j`. -/
theorem robust_le {f : Objective n} {κ c : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {w : Finset (Fin n) → ℝ} (hw : (window f κ c).IsAdditionRobust α w) {j : ℕ}
    (hj : j ≤ n - c) {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (c + j))
    (hcard : T.card ≤ κ) :
    α * f.value T ≤ ∑ S, w S * f.value (S ∪ future n c j) := by
  have hb := le_benchmark f κ c ⟨j, Nat.lt_succ_of_le hj⟩ hT hcard
  have hr := hw.2.2.2 ⟨j, Nat.lt_succ_of_le hj⟩
  exact (mul_le_mul_of_nonneg_left hb hα).trans hr

end ConsistentSubmodular.Checkpoints

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

theorem block_union_future (ℓ c r : ℕ) (hr : r ≤ ℓ) :
    future n c ℓ ∪ future n (c + ℓ) r = future n c (ℓ + r) := by
  ext e
  simp only [future, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

end ConsistentSubmodular.Checkpoints

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ} {α : ℝ}

theorem good_of_weight (hadm : AdmitsAdditionRobust α) (f : Objective n) (P : Params)
    (hh : 0 < P.h) {ω : Sample n P.h} (hω : (sampleLaw hadm f P hh).weight ω ≠ 0) :
    Good P (samplesOf ω.1) (choicesOf ω.2) := by
  have hA := (Law.weight_prod_ne_zero _ _ hω).1
  intro i
  by_cases hi : i < n + 1
  · have hw := Law.weight_pi_ne_zero _ hA ⟨i, hi⟩
    obtain ⟨hsub, hcard⟩ := (robustWeights_spec hadm f P.κ (i * P.ℓ)).2.2.1 _ hw
    simp only [samplesOf, choicesOf, dif_pos hi]
    exact ⟨(ω.2 ⟨i, hi⟩).isLt, hsub, hcard⟩
  · simp only [samplesOf, choicesOf, dif_neg hi]
    exact ⟨hh, Finset.empty_subset _, by simp⟩

end ConsistentSubmodular.Checkpoints

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ} {α : ℝ}

theorem solution (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hadm : AdmitsAdditionRobust α)
    (f : Objective n) {P : Params} {k : ℕ} (hP : P.Valid k) (u : ℕ) (hu : u + 1 ≤ n)
    {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (u + 1)) (hTcard : T.card ≤ P.κ) :
    (1 - 1 / (P.h : ℝ)) * (α * f.value T) ≤
      (sampleLaw hadm f P hP.subblocks_pos).expect
        (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) (u + 1))) := by
  have hℓ := hP.block_pos
  have hh := hP.subblocks_pos
  have hd := Nat.div_add_mod' u P.ℓ
  have hr : u % P.ℓ + 1 ≤ P.ℓ := Nat.mod_lt u hℓ
  set i := u / P.ℓ with hi_def
  set r := u % P.ℓ + 1 with hr_def
  have hit : i * P.ℓ + r = u + 1 := by omega
  have hin : i < n + 1 := by
    have : i ≤ u := Nat.div_le_self u P.ℓ
    omega
  set Z := future n (i * P.ℓ) r with hZ_def
  -- the two options and their indicators
  let Fold : (Fin (n + 1) → Finset (Fin n)) → ℝ :=
    fun a => f.value (oldCore n P.ℓ (samplesOf a) i ∪ Z)
  let Fnew : (Fin (n + 1) → Finset (Fin n)) → ℝ := fun a => f.value (samplesOf a i ∪ Z)
  let G1 : (Fin (n + 1) → Fin P.h) → ℝ :=
    fun b => if r ≤ lo P.ℓ P.h (choicesOf b i) then 1 else 0
  let G2 : (Fin (n + 1) → Fin P.h) → ℝ :=
    fun b => if ¬ r ≤ lo P.ℓ P.h (choicesOf b i) ∧ hi P.ℓ P.h (choicesOf b i) ≤ r then 1 else 0
  set μA := Law.pi fun j : Fin (n + 1) => robustLaw hadm f P.κ (j.val * P.ℓ) with hμA
  set μσ := Law.pi fun _ : Fin (n + 1) => Law.uniform P.h hh with hμσ
  -- pointwise lower bound for choices of positive probability
  have hpoint : (sampleLaw hadm f P hh).expect (fun ω => Fold ω.1 * G1 ω.2 + Fnew ω.1 * G2 ω.2) ≤
      (sampleLaw hadm f P hh).expect
        (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) (u + 1))) := by
    apply Law.expect_mono
    intro ω hω
    have hg := good_of_weight hadm f P hh hω
    have hv := value_le_run hP hg f u
    simp only [Fold, Fnew, G1, G2]
    split_ifs at hv ⊢ <;> linarith
  -- independence: the expectation factorizes
  have hsplit : (sampleLaw hadm f P hh).expect (fun ω => Fold ω.1 * G1 ω.2 + Fnew ω.1 * G2 ω.2) =
      μA.expect Fold * μσ.expect G1 + μA.expect Fnew * μσ.expect G2 := by
    rw [sampleLaw, Law.expect_add, Law.expect_prod_mul, Law.expect_prod_mul]
  -- the subblock probabilities
  have hG : μσ.expect G1 + μσ.expect G2 ≥ 1 - 1 / (P.h : ℝ) := by
    have h1 : μσ.expect G1 = (∑ σ : Fin P.h, (if r ≤ lo P.ℓ P.h σ then 1 else 0 : ℝ)) / P.h := by
      have : G1 = fun b => (fun σ : Fin P.h => (if r ≤ lo P.ℓ P.h σ then 1 else 0 : ℝ))
          (b ⟨i, hin⟩) := by
        funext b
        simp only [G1, choicesOf, dif_pos hin]
      rw [this, hμσ]
      exact (Law.expect_pi_apply (fun _ : Fin (n + 1) => Law.uniform P.h hh) ⟨i, hin⟩
        (fun σ : Fin P.h => (if r ≤ lo P.ℓ P.h σ then 1 else 0 : ℝ))).trans
        (Law.expect_uniform _ _ _)
    have h2 : μσ.expect G2 = (∑ σ : Fin P.h,
        (if ¬ r ≤ lo P.ℓ P.h σ ∧ hi P.ℓ P.h σ ≤ r then 1 else 0 : ℝ)) / P.h := by
      have : G2 = fun b => (fun σ : Fin P.h =>
          (if ¬ r ≤ lo P.ℓ P.h σ ∧ hi P.ℓ P.h σ ≤ r then 1 else 0 : ℝ)) (b ⟨i, hin⟩) := by
        funext b
        simp only [G2, choicesOf, dif_pos hin]
      rw [this, hμσ]
      exact (Law.expect_pi_apply (fun _ : Fin (n + 1) => Law.uniform P.h hh) ⟨i, hin⟩
        (fun σ : Fin P.h =>
          (if ¬ r ≤ lo P.ℓ P.h σ ∧ hi P.ℓ P.h σ ≤ r then 1 else 0 : ℝ))).trans
        (Law.expect_uniform _ _ _)
    have hc := subblock_count P.ℓ P.h r hh
    rw [h1, h2, ← add_div, ← Finset.sum_add_distrib]
    have hhR : (0 : ℝ) < P.h := by exact_mod_cast hh
    have : ((P.h : ℝ) - 1) / P.h = 1 - 1 / P.h := by field_simp
    linarith
  -- the new core: the addition-robust guarantee at the checkpoint `iℓ`
  have hnew : α * f.value T ≤ μA.expect Fnew := by
    have : Fnew = fun a => (fun S => f.value (S ∪ Z)) (a ⟨i, hin⟩) := by
      funext a
      simp only [Fnew, samplesOf, dif_pos hin]
    rw [this, hμA]
    refine le_of_le_of_eq ?_ (Law.expect_pi_apply
      (fun j : Fin (n + 1) => robustLaw hadm f P.κ (j.val * P.ℓ)) ⟨i, hin⟩
      (fun S => f.value (S ∪ Z))).symm
    exact robust_le hα0 (robustWeights_spec hadm f P.κ (i * P.ℓ)) (by omega)
      (by rw [hit]; exact hT) hTcard
  -- the old core: the guarantee at the checkpoint `(i - 1)ℓ`, or all arrivals
  have hold : α * f.value T ≤ μA.expect Fold := by
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · have : Fold = fun _ => f.value Z := by
        funext a
        simp only [Fold, oldCore, if_pos hi0, Finset.empty_union]
      rw [this, Law.expect_const]
      have hZ : T ⊆ Z := by
        intro e he
        have := hT he
        have hi0' : i * P.ℓ = 0 := by rw [hi0, zero_mul]
        rw [hZ_def, hi0']
        simp only [future, arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
          at this ⊢
        omega
      have hmono := f.monotone _ _ hZ
      have hfT := f.nonnegative T
      nlinarith
    · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hjn : j < n + 1 := by omega
      have hjℓ : j * P.ℓ + P.ℓ = i * P.ℓ := by rw [hj]; ring
      have : Fold = fun a => (fun S => f.value (S ∪ future n (j * P.ℓ) (P.ℓ + r)))
          (a ⟨j, hjn⟩) := by
        funext a
        simp only [Fold, oldCore, if_neg (Nat.pos_iff_ne_zero.mp hi0), samplesOf]
        rw [show i - 1 = j by omega, dif_pos hjn, Finset.union_assoc, block, hZ_def, ← hjℓ,
          block_union_future _ _ _ hr]
      rw [this, hμA]
      refine le_of_le_of_eq ?_ (Law.expect_pi_apply
        (fun j : Fin (n + 1) => robustLaw hadm f P.κ (j.val * P.ℓ)) ⟨j, hjn⟩
        (fun S => f.value (S ∪ future n (j * P.ℓ) (P.ℓ + r)))).symm
      exact robust_le hα0 (robustWeights_spec hadm f P.κ (j * P.ℓ)) (by omega)
        (by rw [show j * P.ℓ + (P.ℓ + r) = u + 1 by omega]; exact hT) hTcard
  have hG1 : 0 ≤ μσ.expect G1 := Law.expect_nonneg _ fun b => by
    simp only [G1]; split_ifs <;> norm_num
  have hG2 : 0 ≤ μσ.expect G2 := Law.expect_nonneg _ fun b => by
    simp only [G2]; split_ifs <;> norm_num
  have hαT : 0 ≤ α * f.value T := mul_nonneg hα0 (f.nonnegative T)
  calc (1 - 1 / (P.h : ℝ)) * (α * f.value T)
      ≤ (μσ.expect G1 + μσ.expect G2) * (α * f.value T) :=
        mul_le_mul_of_nonneg_right hG hαT
    _ = μσ.expect G1 * (α * f.value T) + μσ.expect G2 * (α * f.value T) := by ring
    _ ≤ μσ.expect G1 * μA.expect Fold + μσ.expect G2 * μA.expect Fnew :=
        add_le_add (mul_le_mul_of_nonneg_left hold hG1) (mul_le_mul_of_nonneg_left hnew hG2)
    _ = μA.expect Fold * μσ.expect G1 + μA.expect Fnew * μσ.expect G2 := by ring
    _ ≤ _ := by rw [← hsplit]; exact hpoint

end
