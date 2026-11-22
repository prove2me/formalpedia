-- Prove2me | solution 1 for GJKKL.inner_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:09.579515+00:00
-- url     : https://prove2.me/submissions/2fbdda83-8cec-4dcc-8eb5-2f8cca46d155

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Theorems.Thm_GJKKL_not_mem_covered_of_mem_avail
public import Theorems.Thm_GJKKL_avail_subset
public import Theorems.Thm_GJKKL_mem_Dv


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    {dh δ : ℕ → ℝ} {h : List (Finset V)} (ht : Tracked H dh δ h) {v : V} {f : Finset V}
    (hf : f ∈ Dv H h v) :
    ((k : ℝ) - 1) * (dh h.length - δ h.length) ≤ ∑ u ∈ f.erase v, (dv H h u : ℝ) ∧
      ∑ u ∈ f.erase v, (dv H h u : ℝ) ≤ ((k : ℝ) - 1) * (dh h.length + δ h.length) := by
  rw [mem_Dv] at hf
  have hk1 : 1 ≤ k := by
    have := card_pos.mpr ⟨v, hf.2⟩
    rw [hk f (avail_subset H h hf.1)] at this; exact this
  have hcard : ((f.erase v).card : ℝ) = (k : ℝ) - 1 := by
    rw [card_erase_of_mem hf.2, hk f (avail_subset H h hf.1), Nat.cast_sub hk1, Nat.cast_one]
  have hb : ∀ u ∈ f.erase v, |(dv H h u : ℝ) - dh h.length| ≤ δ h.length := fun u hu =>
    ht u (not_mem_covered_of_mem_avail hf.1 (mem_erase.mp hu).2)
  constructor
  · calc ((k : ℝ) - 1) * (dh h.length - δ h.length)
        = ∑ _u ∈ f.erase v, (dh h.length - δ h.length) := by rw [sum_const, nsmul_eq_mul, hcard]
      _ ≤ _ := sum_le_sum fun u hu => by have := hb u hu; rw [abs_le] at this; linarith
  · calc ∑ u ∈ f.erase v, (dv H h u : ℝ) ≤ ∑ _u ∈ f.erase v, (dh h.length + δ h.length) :=
          sum_le_sum fun u hu => by have := hb u hu; rw [abs_le] at this; linarith
      _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]
end GJKKL
