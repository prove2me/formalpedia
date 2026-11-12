-- Prove2me | solution 1 for BunkbedFalse.gadget_eq1_at_half
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:34:27.710761+00:00
-- url     : https://prove2.me/submissions/c6e4ba2c-4c93-49a2-85b5-e87a8bc5a22b

import Theorems.Thm_BunkbedFalse_hyperedge_simulation
import Theorems.Thm_BunkbedFalse_gadget_partition_bound
open Bunkbed Finset

/-- **The gadget at `P = 1/2`, `n = 1204` satisfies Eq. [1] with the constant 400.** -/
theorem solution :
    Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        = Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
    ∧ 0 < Pabc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        - Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
    ∧ 400 * Pa_bc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        ≤ Pabc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        - Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204) := by
  obtain ⟨hsym, hgt⟩ :=
    BunkbedFalse.hyperedge_simulation 1204 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hz, -⟩ :=
    BunkbedFalse.gadget_partition_bound 1204 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hzpos : (0 : ℚ) < Pa_bc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204) := by
    rw [hz]; positivity
  have hc : ((1204 : ℕ) : ℚ) * (1 - 1 / 2) / (1 + 1 / 2) - 1 = 1201 / 3 := by norm_num
  rw [hc] at hgt
  refine ⟨hsym, ?_, ?_⟩
  · nlinarith [hgt, hzpos]
  · nlinarith [hgt, hzpos]
