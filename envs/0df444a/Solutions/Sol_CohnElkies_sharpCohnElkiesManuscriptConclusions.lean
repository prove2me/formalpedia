-- Prove2me | solution 1 for CohnElkies.sharpCohnElkiesManuscriptConclusions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/d05d1e47-a420-41f9-b0e8-1528ade2da58

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalBinaryExponent_pos
import Theorems.Thm_CohnElkies_sharpQuotientAsymptotic
import Theorems.Thm_CohnElkies_sharpPackingRootAsymptotic
import Theorems.Thm_CohnElkies_sharpLogAsymptotic
import Theorems.Thm_CohnElkies_sharpBinaryLogAsymptotic
import Theorems.Thm_CohnElkies_manuscriptQuotientRootInf_div_sqrt_tendsto
import Theorems.Thm_CohnElkies_exists_manuscriptQuotientRootIsLittleO
import Theorems.Thm_CohnElkies_exists_manuscriptPackingIsLittleO
import Theorems.Thm_CohnElkies_exists_manuscriptUniversalPackingIsLittleO
import Theorems.Thm_CohnElkies_exists_manuscriptBinaryIsLittleO
import Theorems.Thm_CohnElkies_criticalBinaryExponent_mem_Ioo_d30
import Theorems.Thm_CohnElkies_manuscriptQuotientRootSet_eq_literal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
open CohnElkies
namespace CohnElkies
theorem _root_.solution :
    SharpCohnElkiesManuscriptConclusions := by
  refine
    { root_before_infimum := ?_
      root_before_infimum_vanishing_error := ?_
      linear_program_root := ?_
      natural_logarithmic_rate := ?_
      natural_vanishing_exponential_error := ?_
      universal_nonnegative_delta := ?_
      base_two_exponent_positive := ?_
      base_two_decimal_certificate := ?_
      base_two_logarithmic_rate := ?_
      base_two_vanishing_exponential_error := ?_ }
  · simp_rw [← manuscriptQuotientRootSet_eq_literal]
    simpa [one_div] using
      (manuscriptQuotientRootInf_div_sqrt_tendsto
        sharpQuotientAsymptotic)
  · obtain ⟨err, herr, hformula⟩ :=
      exists_manuscriptQuotientRootIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, ?_⟩
    intro d hd
    rw [← manuscriptQuotientRootSet_eq_literal]
    simpa [one_div] using hformula d hd
  · simpa [SharpPackingRootAsymptotic, criticalPackingBase] using
      sharpPackingRootAsymptotic
  · simpa [SharpLogAsymptotic] using sharpLogAsymptotic
  · obtain ⟨err, herr, hformula⟩ := exists_manuscriptPackingIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    simpa [criticalPackingBase] using hformula d hd
  · obtain ⟨δ, hδ, hnonneg, hbound⟩ :=
      exists_manuscriptUniversalPackingIsLittleO
    refine ⟨δ, (Asymptotics.isLittleO_one_iff ℝ).mp hδ, hnonneg, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd f
    simpa [criticalPackingBase] using hbound d hd f
  · simpa [criticalBinaryExponent] using criticalBinaryExponent_pos
  · simpa [criticalBinaryExponent] using
      criticalBinaryExponent_mem_Ioo_d30
  · simpa [SharpBinaryLogAsymptotic, criticalBinaryExponent] using
      sharpBinaryLogAsymptotic
  · obtain ⟨err, herr, hformula⟩ := exists_manuscriptBinaryIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, ?_⟩
    simpa [criticalBinaryExponent] using hformula
end CohnElkies
