-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.assembleLattices
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:29.053906+00:00
-- url     : https://prove2.me/submissions/b66588c0-815d-4c19-a460-9cd92d893055

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_rd_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution : AssembleLattices := by
  intro hdeg hC hU hB hI hDs hDp hN hCov E _ _ _ hUn g ν s hg
  have hUA := (hU E hUn).2 g
  have hb := hB E (idl E g 1 ν) (idl E g 2 ν) s (idl_le E g ν) (hC E g 2 ν)
  have hi := hI E (idl E g 1 ν) g s (idl_ne_zero E g 1 ν hg) (hC E g 1 ν) hg hUA
  rw [idl_mul E g 1 ν hg, show (1 : ℤ) + 1 = 2 from rfl] at hi
  have hd : dualLat E g (perLat E g ν s)
      = twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1) :=
    le_antisymm (hDs E g ν s hg) (hDp E hUn g ν s hg)
  have hi2 := hI E (dualIdl E g ν) g (s + 1) (idl_ne_zero E g _ _ hg) (hC E g _ _) hg hUA
  have hi3 := hI E (liftIdl E g ν) g s (idl_ne_zero E g _ _ hg) (hC E g _ _) hg hUA
  unfold dualIdl at hi2
  unfold liftIdl at hi3
  rw [idl_mul E g (-1) _ hg, show (-1 : ℤ) + 1 = 0 from rfl] at hi2 hi3
  have hrd : 0 < rd E := rd_pos E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hcov := hCov E (idl E g 2 ν) (perLat E g ν s) (rd E ^ (-ν)) (idl_ne_zero E g 2 ν hg)
    (zpow_ne_zero _ hrd.ne') hb.1 (by
      have : idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E := hi.2
      rw [this]; positivity)
  refine ⟨hb.1, hb.2, hi.1, hi.2, ?_, ?_, inf_le_left, hi3.1, ?_, hcov.1, hcov.2.1, ?_⟩
  · rw [hd]; exact inf_le_left
  · rw [hd]; exact hi2.1
  · unfold dualIdl
    rw [hN E g (-1) (-(ν + 1)) hg, zpow_neg, zpow_neg, zpow_neg, zpow_one, ← mul_inv, inv_pow,
      zpow_natCast]
  · rw [hcov.2.2]
    have h4 : idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E := hi.2
    rw [h4]
    have hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
    have hsq : √((|discr E| : ℤ) : ℝ) = rd E ^ deg E := by
      unfold rd
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]
      congr 1
      rw [(hdeg E).1]
      have : (deg E : ℝ) ≠ 0 := by exact_mod_cast (hdeg E).2.2.ne'
      push_cast; field_simp
    have hNB : (FractionalIdeal.absNorm (idl E g 2 ν) : ℝ)
        = (((g : ℝ) ^ (2 : ℤ) * rd E ^ ν) ^ deg E) ^ 2 := by
      rw [← hN E g 2 ν hg, Real.sq_sqrt]
      exact_mod_cast (FractionalIdeal.absNorm_nonneg _)
    rw [hsq, hNB, abs_of_pos (zpow_pos hrd _), zpow_neg]
    have ha : 0 < rd E ^ ν := zpow_pos hrd _
    set a := rd E ^ ν
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    push_cast
    have hG : (g : ℝ) ^ deg E ≠ 0 := by positivity
    have hA : a ^ deg E ≠ 0 := by positivity
    rw [inv_pow, inv_pow, div_pow, pow_mul, mul_pow, mul_pow]
    field_simp
    ring
end Formalism.FourierDecayAlt.P.S6x2
