-- Prove2me | solution 1 for BunkbedFalse.explicit_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T06:52:18.626896+00:00
-- url     : https://prove2.me/submissions/484ffebe-3c12-4abb-95e6-563dfe1da4ab

import Theorems.Thm_BunkbedFalse_sub_invariants
import Theorems.Thm_BunkbedFalse_gadget_eq1_at_half
import Theorems.Thm_BunkbedFalse_robust_hyperedge
import Theorems.Thm_BunkbedAux_partition_sum_eq_total
import Theorems.Thm_BunkbedAux_sum_weight_eq_one
import Theorems.Thm_BunkbedAux_probOf_mem_unitInterval
import Theorems.Thm_BunkbedFalse_sub_probability_transfer

open Bunkbed Bunkbed.Hyper Bunkbed.Sub BunkbedFalse

theorem solution :
    ∃ (E : Finset (Sym2 (Fin 7222))) (T : Finset (Fin 7222)) (u v : Fin 7222),
      (ofEdges E).edgeFinset.card = 14442 ∧ T.card = 3 ∧ (ofEdges E).Connected ∧
      bbProb E (fun _ => (1 / 2 : ℚ)) T (u, 0) (v, 0)
        < bbProb E (fun _ => (1 / 2 : ℚ)) T (u, 0) (v, 1) := by
  let E := gadgetE 1204
  let w := gadgetW 1204 (1/2)
  let P : WZ → ℚ := fun s => match s with
    | .abc => Pabc E w 0 1 (Fin.last 1204)
    | .ab_c => Pab_c E w 0 1 (Fin.last 1204)
    | .ac_b => Pac_b E w 0 1 (Fin.last 1204)
    | .a_bc => Pa_bc E w 0 1 (Fin.last 1204)
    | .a_b_c => Pa_b_c E w 0 1 (Fin.last 1204)
  have hw0 : ∀ e, 0 ≤ w e := by
    intro e
    dsimp [w, gadgetW]
    split_ifs <;> norm_num
  have hw1 : ∀ e, w e ≤ 1 := by
    intro e
    dsimp [w, gadgetW]
    split_ifs <;> norm_num
  have hnn : ∀ s, 0 ≤ P s := by
    intro s
    cases s <;> exact (BunkbedAux.probOf_mem_unitInterval E w hw0 hw1 _).1
  have hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1 := by
    have h := BunkbedAux.partition_sum_eq_total E w 0 1 (Fin.last 1204)
    rw [BunkbedAux.sum_weight_eq_one] at h
    change Pabc E w 0 1 (Fin.last 1204) + Pa_b_c E w 0 1 (Fin.last 1204) +
      Pa_bc E w 0 1 (Fin.last 1204) + Pab_c E w 0 1 (Fin.last 1204) +
      Pac_b E w 0 1 (Fin.last 1204) = 1
    linarith
  have hcond := gadget_eq1_at_half
  have hlt := robust_hyperedge P hnn hsum hcond.1 hcond.2.1 hcond.2.2
  refine ⟨subEdges, subT, iota 0, iota 9, sub_invariants.1,
    sub_invariants.2.1, sub_invariants.2.2, ?_⟩
  rw [sub_probability_transfer P rfl rfl rfl rfl rfl,
      sub_probability_transfer P rfl rfl rfl rfl rfl]
  exact hlt

