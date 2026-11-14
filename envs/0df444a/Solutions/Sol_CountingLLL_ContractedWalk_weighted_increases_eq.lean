-- Prove2me | solution 1 for CountingLLL.ContractedWalk.weighted_increases_eq
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:58:24.286348+00:00
-- url     : https://prove2.me/submissions/3e244c51-1da1-4166-b7b2-dd8f2a331b4c

import Definitions.Def_CountingLLL_ContractedCost
import Theorems.Thm_CountingLLL_ContractedWalk_weighted_fresh_bit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

private theorem weighted_fresh_bits_sum (p : ℝ≥0∞) (hp : p ≤ 1)
    (F : (t : ℕ) → ((Finset.range t) → Bool) → ℝ≥0∞) :
    (∫⁻ ω : Tape, ∑' t, F t (fun j => ω j) * (if ω t then 1 else 0) ∂tapeLaw p) =
      (∫⁻ ω : Tape, ∑' t, F t (fun j => ω j) ∂tapeLaw p) * p := by
  classical
  have hf (t : ℕ) : Measurable (fun ω : Tape => F t (fun j => ω j)) := by
    apply Measurable.comp (Measurable.of_discrete : Measurable (F t))
    exact measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  have hb (t : ℕ) : Measurable (fun ω : Tape => if ω t then (1:ℝ≥0∞) else 0) := by
    exact (Measurable.ite ((MeasurableSet.singleton true).preimage (measurable_pi_apply t)) measurable_const measurable_const)
  have hm (t : ℕ) : AEMeasurable (fun ω : Tape => F t (fun j => ω j) * (if ω t then 1 else 0)) (tapeLaw p) :=
    ((hf t).mul (hb t)).aemeasurable
  rw [lintegral_tsum hm]
  simp_rw [weighted_fresh_bit p hp]
  rw [lintegral_tsum (fun t => (hf t).aemeasurable), ENNReal.tsum_mul_right]

private theorem level_ext (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) : level ω i t = level ω' i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ k < t, ω k = ω' k := by intro k hk; exact h k (by omega)
    have hnow := h t (by omega)
    simp only [level, ih hprev, hnow]

private theorem upward_ext (ω ω' : Tape) (i t : ℕ) (h : ∀ k < t, ω k = ω' k) :
    upwardBefore ω i t = upwardBefore ω' i t := by
  unfold upwardBefore
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hl : level ω i k = level ω' i k := level_ext ω ω' i k (by intro j hj; exact h j (by omega))
  rw [hl, h k hk']

/-- Expected weighted upward changes are θ times all weighted changes. -/
theorem solution (p : ℝ≥0∞) (hp : p ≤ 1) (i j : ℕ) :
    expectedWeightedIncreases p i j = expectedWeightedChanges p i j * p := by
  classical
  let ext : (t : ℕ) → ((Finset.range t) → Bool) → Tape := fun t x k =>
    if h : k < t then x ⟨k, Finset.mem_range.mpr h⟩ else false
  let F : (t : ℕ) → ((Finset.range t) → Bool) → ℝ≥0∞ := fun t x => changeWeight (ext t x) i j t
  have heq (t : ℕ) (ω : Tape) : F t (fun k => ω k) = changeWeight ω i j t := by
    have h : ∀ k < t, (ext t (fun k => ω k)) k = ω k := by intro k hk; simp [ext, hk]
    unfold F changeWeight
    rw [level_ext _ _ i t h, upward_ext _ _ i t h]
  have h := weighted_fresh_bits_sum p hp F
  unfold expectedWeightedChanges expectedWeightedIncreases weightedChanges weightedIncreases
  simpa only [heq] using h

