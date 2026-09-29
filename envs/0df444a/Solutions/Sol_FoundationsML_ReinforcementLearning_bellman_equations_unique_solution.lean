-- Prove2me | solution 1 for FoundationsML.ReinforcementLearning.bellman_equations_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T00:43:49.201979+00:00
-- url     : https://prove2.me/submissions/9395a4a7-bd31-4faa-b391-0df427dc7424

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

open Matrix

namespace FoundationsML.ReinforcementLearning

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

lemma bu_Q_nonneg {π : S → A → ℝ} (hπ : IsPolicy π) {P : S → A → S → ℝ}
    (hP : IsTransitionKernel P) (s s' : S) : 0 ≤ InducedTransition π P s s' :=
  Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')

lemma bu_Q_row {π : S → A → ℝ} (hπ : IsPolicy π) {P : S → A → S → ℝ}
    (hP : IsTransitionKernel P) (s : S) : ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
  exact (hπ s).2

/-- Powers of a row-stochastic matrix are row-stochastic. -/
lemma bu_pow_stoch (Q : Matrix S S ℝ) (h0 : ∀ i j, 0 ≤ Q i j) (h1 : ∀ i, ∑ j, Q i j = 1)
    (t : ℕ) : (∀ i j, 0 ≤ (Q ^ t) i j) ∧ ∀ i, ∑ j, (Q ^ t) i j = 1 := by
  induction t with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ t ih =>
    rw [pow_succ]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun k _ => mul_nonneg (ih.1 i k) (h0 k j)
    · simp_rw [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, h1, mul_one]
      exact ih.2 i

/-- The state-occupation distribution is a row of a matrix power. -/
lemma bu_occ (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (x : S) :
    OccupationDist π P s0 t x = ((Matrix.of (InducedTransition π P)) ^ t) s0 x := by
  induction t generalizing x with
  | zero => simp [OccupationDist, Matrix.one_apply, eq_comm]
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [OccupationDist, ih, Matrix.of_apply]

lemma bu_pv (π : S → A → ℝ) (P : S → A → S → ℝ) (Er : S → A → ℝ) (γ : ℝ) (s0 : S) :
    PolicyValue π P Er γ s0 = ∑' t : ℕ, γ ^ t *
      ((Matrix.of (InducedTransition π P)) ^ t *ᵥ InducedReward π Er) s0 := by
  unfold PolicyValue
  congr 1; funext t; congr 1
  simp only [Matrix.mulVec, dotProduct, bu_occ]

/-- The only vector fixed by `v = γ Q v` (for a stochastic `Q` and `0 ≤ γ < 1`) is `0`. -/
lemma bu_fix_zero (Q : Matrix S S ℝ) (h0 : ∀ i j, 0 ≤ Q i j) (h1 : ∀ i, ∑ j, Q i j = 1)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (v : S → ℝ)
    (hv : (1 - γ • Q) *ᵥ v = 0) : v = 0 := by
  rcases isEmpty_or_nonempty S with hS | hS
  · funext s; exact isEmptyElim s
  obtain ⟨s0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun s => |v s|)
    Finset.univ_nonempty
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hv
  have hfix : ∀ s, v s = γ * ∑ j, Q s j * v j := by
    intro s
    have := congrFun hv s
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.mulVec,
      dotProduct] at this
    linarith
  have hsb : |∑ j, Q s0 j * v j| ≤ |v s0| := by
    calc |∑ j, Q s0 j * v j| ≤ ∑ j, |Q s0 j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, Q s0 j * |v j| := by
          refine Finset.sum_congr rfl fun j _ => ?_; rw [abs_mul, abs_of_nonneg (h0 s0 j)]
      _ ≤ ∑ j, Q s0 j * |v s0| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j))
            (h0 s0 j)
      _ = |v s0| := by rw [← Finset.sum_mul, h1, one_mul]
  have hb : |v s0| ≤ γ * |v s0| := by
    calc |v s0| = |γ * ∑ j, Q s0 j * v j| := by rw [← hfix s0]
      _ = γ * |∑ j, Q s0 j * v j| := by rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ γ * |v s0| := mul_le_mul_of_nonneg_left hsb hγ0
  have hz : |v s0| = 0 := by
    have := abs_nonneg (v s0)
    nlinarith
  funext s
  have := hmax s (Finset.mem_univ s)
  rw [hz] at this
  exact abs_nonpos_iff.mp this

theorem bu_main (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsUnit (1 - γ • (Matrix.of (InducedTransition π P))) ∧
    (fun s => PolicyValue π P Er γ s) =
      (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er ∧
    ∀ V : S → ℝ,
      (∀ s : S, V s = InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * V s') →
        V = (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er := by
  set Q := Matrix.of (InducedTransition π P) with hQ
  set R := InducedReward π Er with hR
  have h0 : ∀ i j, 0 ≤ Q i j := fun i j => bu_Q_nonneg hπ hP i j
  have h1 : ∀ i, ∑ j, Q i j = 1 := fun i => bu_Q_row hπ hP i
  -- invertibility
  have hunit : IsUnit (1 - γ • Q) := by
    refine Matrix.mulVec_injective_iff_isUnit.mp fun v w hvw => ?_
    have := bu_fix_zero Q h0 h1 hγ0 hγ1 (v - w) (by rw [Matrix.mulVec_sub, hvw, sub_self])
    exact sub_eq_zero.mp this
  have hdet : IsUnit (1 - γ • Q).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  -- uniqueness
  have huniq : ∀ V : S → ℝ, (∀ s : S, V s = R s + γ * ∑ s' : S, InducedTransition π P s s' * V s') →
      V = (1 - γ • Q)⁻¹ *ᵥ R := by
    intro V hV
    have hMV : (1 - γ • Q) *ᵥ V = R := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      funext s
      have := hV s
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hQ,
        Matrix.of_apply]
      linarith
    rw [← hMV, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  refine ⟨hunit, ?_, huniq⟩
  -- the policy value satisfies Bellman's equations
  apply huniq
  intro s0
  set B := ∑ x, |R x| with hB
  have hbound : ∀ (t : ℕ) (s : S), |((Q ^ t) *ᵥ R) s| ≤ B := by
    intro t s
    obtain ⟨p0, p1⟩ := bu_pow_stoch Q h0 h1 t
    simp only [Matrix.mulVec, dotProduct]
    calc |∑ j, (Q ^ t) s j * R j| ≤ ∑ j, |(Q ^ t) s j * R j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, (Q ^ t) s j * |R j| := by
          refine Finset.sum_congr rfl fun j _ => ?_; rw [abs_mul, abs_of_nonneg (p0 s j)]
      _ ≤ ∑ j, (Q ^ t) s j * B :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun x => |R x|) (fun x _ => abs_nonneg _)
              (Finset.mem_univ j)) (p0 s j)
      _ = B := by rw [← Finset.sum_mul, p1, one_mul]
  have hsum : ∀ s : S, Summable (fun t : ℕ => γ ^ t * ((Q ^ t) *ᵥ R) s) := by
    intro s
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0 hγ1).mul_right B)
      fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    exact mul_le_mul_of_nonneg_left (hbound t s) (pow_nonneg hγ0 t)
  have hpv : ∀ s, PolicyValue π P Er γ s = ∑' t : ℕ, γ ^ t * ((Q ^ t) *ᵥ R) s :=
    fun s => bu_pv π P Er γ s
  show PolicyValue π P Er γ s0 = R s0 + γ * ∑ s', InducedTransition π P s0 s' *
    PolicyValue π P Er γ s'
  rw [hpv, (hsum s0).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, Matrix.one_mulVec]
  congr 1
  simp_rw [hpv]
  have hstep : ∀ t : ℕ, γ ^ (t + 1) * ((Q ^ (t + 1)) *ᵥ R) s0 =
      γ * ∑ s', InducedTransition π P s0 s' * (γ ^ t * ((Q ^ t) *ᵥ R) s') := by
    intro t
    rw [pow_succ' Q, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hQ, Matrix.of_apply]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  simp_rw [hstep]
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun s' _ => (hsum s').mul_left _)]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [tsum_mul_left]

end FoundationsML.ReinforcementLearning

open FoundationsML.ReinforcementLearning

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsUnit (1 - γ • (Matrix.of (InducedTransition π P))) ∧
    (fun s => PolicyValue π P Er γ s) =
      (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er ∧
    ∀ V : S → ℝ,
      (∀ s : S, V s = InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * V s') →
        V = (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er :=
  bu_main π hπ P hP Er γ hγ0 hγ1
