-- Prove2me | solution 2 for BunkbedFalse.explicit_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T13:29:48.05792+00:00
-- url     : https://prove2.me/submissions/e16f64f4-5023-4dbb-9268-0d09de70e99f

import Theorems.Thm_BunkbedFalse_simulation
import Theorems.Thm_BunkbedFalse_sub_invariants
import Theorems.Thm_BunkbedFalse_robust_hyperedge
import Theorems.Thm_BunkbedFalse_gadget_eq1_at_half
import Theorems.Thm_BunkbedAux_partition_sum_eq_total
import Theorems.Thm_BunkbedAux_sum_weight_eq_one
import Theorems.Thm_BunkbedAux_probOf_mem_unitInterval

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option autoImplicit false

open Bunkbed Bunkbed.Hyper Finset SimpleGraph

private lemma gw_nonneg : ∀ e, 0 ≤ gadgetW 1204 (1 / 2 : ℚ) e := by
  intro e; simp only [gadgetW]; split <;> norm_num

private lemma gw_le_one : ∀ e, gadgetW 1204 (1 / 2 : ℚ) e ≤ 1 := by
  intro e; simp only [gadgetW]; split <;> norm_num

/-- **Theorem 1.2 of Gladkov-Pak-Zimin** (planarity omitted). -/
theorem solution :
    ∃ (E : Finset (Sym2 (Fin 7222))) (T : Finset (Fin 7222)) (u v : Fin 7222),
      (ofEdges E).edgeFinset.card = 14442 ∧ T.card = 3 ∧ (ofEdges E).Connected ∧
      bbProb E (fun _ => (1 / 2 : ℚ)) T (u, 0) (v, 0)
        < bbProb E (fun _ => (1 / 2 : ℚ)) T (u, 0) (v, 1) := by
  obtain ⟨hcard, hT, hconn⟩ := BunkbedFalse.sub_invariants
  refine ⟨Bunkbed.Sub.subEdges, Bunkbed.Sub.subT, Bunkbed.Sub.iota 0, Bunkbed.Sub.iota 9,
    hcard, hT, hconn, ?_⟩
  rw [BunkbedFalse.simulation 0 9 0, BunkbedFalse.simulation 0 9 1]
  refine BunkbedFalse.robust_hyperedge _ ?_ ?_ ?_ ?_ ?_
  · intro s
    cases s <;>
      simp only [Pabc, Pa_b_c, Pa_bc, Pab_c, Pac_b] <;>
      exact (BunkbedAux.probOf_mem_unitInterval _ _ gw_nonneg gw_le_one _).1
  · have h1 := BunkbedAux.partition_sum_eq_total (gadgetE 1204) (gadgetW 1204 (1 / 2))
      (0 : Fin 1205) 1 (Fin.last 1204)
    rw [BunkbedAux.sum_weight_eq_one] at h1
    simp only
    linarith [h1]
  · exact BunkbedFalse.gadget_eq1_at_half.1
  · exact BunkbedFalse.gadget_eq1_at_half.2.1
  · exact BunkbedFalse.gadget_eq1_at_half.2.2

#print axioms solution
