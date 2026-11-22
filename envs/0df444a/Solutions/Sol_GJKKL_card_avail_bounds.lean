-- Prove2me | solution 1 for GJKKL.card_avail_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:44.868797+00:00
-- url     : https://prove2.me/submissions/c3d274ff-0444-42a2-a29b-af8f3dcc5e61

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Theorems.Thm_GJKKL_card_uncovered
public import Theorems.Thm_GJKKL_mem_uncovered
public import Theorems.Thm_GJKKL_sum_uncovered_dv


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k) (hk0 : 0 < k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (hh : IsGreedySeq H h) (ht : Tracked H dh δ h) :
    ((Fintype.card V : ℝ) - k * h.length) / k * (dh h.length - δ h.length) ≤ (avail H h).card ∧
      ((avail H h).card : ℝ) ≤
        ((Fintype.card V : ℝ) - k * h.length) / k * (dh h.length + δ h.length) := by
  have hsum := sum_uncovered_dv H hk h
  have hunc := card_uncovered hk hh
  have hsumR : ∑ u ∈ uncovered h, (dv H h u : ℝ) = k * (avail H h).card := by
    exact_mod_cast hsum
  have huncR : ((uncovered h).card : ℝ) = (Fintype.card V : ℝ) - k * h.length := by
    have : ((uncovered h).card : ℝ) + k * h.length = Fintype.card V := by exact_mod_cast hunc
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hlo : ∑ _u ∈ uncovered h, (dh h.length - δ h.length) ≤ ∑ u ∈ uncovered h, (dv H h u : ℝ) :=
    sum_le_sum fun u hu => by
      have := ht u (mem_uncovered.mp hu); rw [abs_le] at this; linarith
  have hhi : ∑ u ∈ uncovered h, (dv H h u : ℝ) ≤ ∑ _u ∈ uncovered h, (dh h.length + δ h.length) :=
    sum_le_sum fun u hu => by
      have := ht u (mem_uncovered.mp hu); rw [abs_le] at this; linarith
  rw [sum_const, nsmul_eq_mul, huncR, hsumR] at hlo hhi
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hkR]; linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ hkR]; linarith
end GJKKL
