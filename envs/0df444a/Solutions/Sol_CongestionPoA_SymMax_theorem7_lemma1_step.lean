-- Prove2me | solution 1 for CongestionPoA.SymMax.theorem7_lemma1_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:25:53.690173+00:00
-- url     : https://prove2.me/submissions/880bd9e5-4b04-459e-a327-3c851ec2470c

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

set_option autoImplicit false

namespace CongestionPoA.SymMax.P2680

theorem key_ineq (x y : ℕ) :
    (x : ℝ) * ((y : ℝ) + 1) ≤ 1 / 3 * ((y : ℝ) * y) + 5 / 3 * ((x : ℝ) * x) := by
  have h : (3 * x * (y + 1) : ℤ) ≤ y * y + 5 * x * x := by
    rcases Nat.lt_or_ge x 2 with hx | hx
    · interval_cases x
      · simp; positivity
      · rcases Nat.lt_or_ge y 2 with hy | hy
        · interval_cases y <;> norm_num
        · have : (2 : ℤ) ≤ y := by exact_mod_cast hy
          push_cast
          nlinarith [mul_nonneg (sub_nonneg.mpr this) (by linarith : (0:ℤ) ≤ (y:ℤ) - 1)]
    · have : (2 : ℤ) ≤ x := by exact_mod_cast hx
      nlinarith [sq_nonneg (2 * (y : ℤ) - 3 * x)]
  have h' : ((3 * x * (y + 1) : ℤ) : ℝ) ≤ ((y * y + 5 * x * x : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

theorem sumCost_eq {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A : ι → Finset E) :
    sumCost G A = ∑ e, (load A e : ℝ) * G.latency e (load A e) := by
  unfold sumCost cost
  calc ∑ i, ∑ e ∈ A i, G.latency e (load A e)
      = ∑ i, ∑ e, (if e ∈ A i then G.latency e (load A e) else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_ite_mem]; simp
    _ = ∑ e, ∑ i, (if e ∈ A i then G.latency e (load A e) else 0) := Finset.sum_comm
    _ = ∑ e, (load A e : ℝ) * G.latency e (load A e) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [← Finset.sum_filter]; simp [load]

end CongestionPoA.SymMax.P2680

open CongestionPoA.SymMax in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E) (hlin : IsLinear G) :
    ∑ e, (load P e : ℝ) * G.latency e (load A e + 1) ≤
      1 / 3 * sumCost G A + 5 / 3 * sumCost G P := by
  rw [CongestionPoA.SymMax.P2680.sumCost_eq, CongestionPoA.SymMax.P2680.sumCost_eq,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  obtain ⟨a, b, ha, hb, hab⟩ := hlin
  rw [hab, hab, hab]
  push_cast
  have k := CongestionPoA.SymMax.P2680.key_ineq (load P e) (load A e)
  have hx : (0 : ℝ) ≤ (load P e : ℝ) := Nat.cast_nonneg _
  have hy : (0 : ℝ) ≤ (load A e : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left k (ha e), mul_nonneg (hb e) hx, mul_nonneg (hb e) hy]
