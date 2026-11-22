-- Prove2me | solution 1 for GJKKL.lossSum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:31.478927+00:00
-- url     : https://prove2.me/submissions/2b9a2ad7-acb4-40b5-b2e5-31c6817d3f42

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
public import Theorems.Thm_GJKKL_lossSum_eq
public import Theorems.Thm_GJKKL_card_hitters_le
public import Theorems.Thm_GJKKL_card_hitters_ge
public import Theorems.Thm_GJKKL_avail_subset
public import Theorems.Thm_GJKKL_mem_Dv


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k : ℕ} (hk : IsUniform H k)
    (h : List (Finset V)) (v : V) {c : ℕ} (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    lossSum H h v ≤ ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, dv H h u ∧
      ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, dv H h u ≤
        lossSum H h v + (Dv H h v).card * ((k - 1) * c + (k - 1) * (k - 2) * c) := by
  rw [lossSum_eq]
  refine ⟨sum_le_sum fun f _ => card_hitters_le H h v f, ?_⟩
  have hcard : ∀ f ∈ Dv H h v, (f.erase v).card = k - 1 := by
    intro f hf
    rw [mem_Dv] at hf
    rw [card_erase_of_mem hf.2, hk f (avail_subset H h hf.1)]
  calc ∑ f ∈ Dv H h v, ∑ u ∈ f.erase v, dv H h u
      ≤ ∑ f ∈ Dv H h v, ((hitters H h v f).card + ((k - 1) * c + (k - 1) * (k - 2) * c)) := by
        refine sum_le_sum fun f hf => ?_
        have := card_hitters_ge H h v f hc
        rw [hcard f hf] at this
        have hk2 : k - 1 - 1 = k - 2 := by omega
        rw [hk2] at this
        omega
    _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
end GJKKL
