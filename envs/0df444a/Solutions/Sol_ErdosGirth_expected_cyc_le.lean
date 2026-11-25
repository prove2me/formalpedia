-- Prove2me | solution 1 for ErdosGirth.expected_cyc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:13.984804+00:00
-- url     : https://prove2.me/submissions/2a8761db-92a1-4274-8ab8-f71ae1d59dd0

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_sum_wt_cycle
public import Theorems.Thm_ErdosGirth_sum_cycle_le

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical
namespace ErdosGirth
theorem _root_.solution {m : ℕ} (g : ℕ) {p : ℝ} (hp0 : 0 ≤ p) :
    ∑ S ∈ (pairs m).powerset, wt m p S * ∑ u, cyc m g S u
      ≤ ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ := by
  calc ∑ S ∈ (pairs m).powerset, wt m p S * ∑ u, cyc m g S u
      = ∑ S ∈ (pairs m).powerset, ∑ u, ∑ ℓ ∈ range (g + 1),
          ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
            wt m p S * (if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0) := by
        simp_rw [cyc, mul_sum]
    _ = ∑ ℓ ∈ range (g + 1), ∑ u, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
          ∑ S ∈ (pairs m).powerset,
            wt m p S * (if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0) := by
        refine sum_comm.trans ?_
        refine (sum_congr rfl fun u _ => sum_comm).trans ?_
        refine (sum_congr rfl fun u _ => sum_congr rfl fun ℓ _ => sum_comm).trans ?_
        exact sum_comm
    _ = ∑ ℓ ∈ range (g + 1), ∑ u, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
          (if c.IsCycle then p ^ ℓ else 0) := by
        refine sum_congr rfl fun ℓ _ => sum_congr rfl fun u _ => sum_congr rfl fun c hc => ?_
        rw [sum_wt_cycle, mem_finsetWalkLength_iff.mp hc]
    _ ≤ _ := sum_le_sum fun ℓ _ => sum_cycle_le hp0 ℓ
end ErdosGirth
