-- Prove2me | solution 1 for GJKKL.lossSum_le_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:48.575864+00:00
-- url     : https://prove2.me/submissions/5f25f1de-0ce8-4768-bce5-44a95df8fa80

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Theorems.Thm_GJKKL_inner_sum_bounds
public import Theorems.Thm_GJKKL_lossSum_bounds


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (ht : Tracked H dh δ h) (v : V) {c : ℕ}
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    (lossSum H h v : ℝ) ≤ (dv H h v : ℝ) * ((k : ℝ) - 1) * (dh h.length + δ h.length) := by
  have hb := (lossSum_bounds H hk h v hc).1
  have hbR : (lossSum H h v : ℝ) ≤ ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, (dv H h u : ℝ) := by
    exact_mod_cast hb
  refine hbR.trans ?_
  calc ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, (dv H h u : ℝ)
      ≤ ∑ _f ∈ Dv H h v, ((k : ℝ) - 1) * (dh h.length + δ h.length) :=
        sum_le_sum fun f hf => (inner_sum_bounds H hk ht hf).2
    _ = _ := by rw [sum_const, nsmul_eq_mul, dv]; ring
end GJKKL
