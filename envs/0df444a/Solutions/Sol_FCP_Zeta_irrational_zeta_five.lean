-- Prove2me | solution 1 for FCP.Zeta.irrational_zeta_five
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T23:27:29.303878+00:00
-- url     : https://prove2.me/submissions/2bf48c5d-90e8-4197-b6ab-24709c6a25ee

import Definitions.Def_Zeta5_SourceValue
import Theorems.Thm_Apery_irrational_of_eventually_exists_int_poly
import Theorems.Thm_Apery_tendsto_pow_mul_exp_neg_sq_of_pos
import Theorems.Thm_Apery_main_estimate

open Polynomial Filter Topology

theorem solution : ∃ x : ℝ, Irrational x ∧ riemannZeta 5 = x := by
  obtain ⟨c, hc, h⟩ := Apery.main_estimate
  refine ⟨Apery.zeta5, ?_, Apery.riemannZeta_five⟩
  exact Apery.irrational_of_eventually_exists_int_poly Apery.zeta5 (fun n => 37 * n)
    (fun n => Real.exp (-c * (n : ℝ) ^ 2))
    (Apery.tendsto_pow_mul_exp_neg_sq_of_pos hc)
    (h.mono fun _ ⟨Q, _, hdeg, hpos, hlt⟩ => ⟨Q, hdeg.le, hpos, hlt.le⟩)
