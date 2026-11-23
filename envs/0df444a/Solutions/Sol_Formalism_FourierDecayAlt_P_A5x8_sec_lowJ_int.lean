-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_lowJ_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:43.926317+00:00
-- url     : https://prove2.me/submissions/4d0adb6c-ba7b-4423-86b1-259a1bcbec58

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_vecMul_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) (a : lowW K h.1 h.2) (ρ : Fin h.1.sum → K) :
    sec_lowJ h c a ρ ∈ intSub R (lowW K (addBlock h 1 c).1 (addBlock h 1 c).2) ↔
      a ∈ intSub R (lowW K h.1 h.2) ∧ ∀ j, ρ j ∈ R := by
  have hd1 : (sec_m (sec_lowJ h c a ρ)).det = 1 := isLowUni_det K (sec_lowJ h c a ρ).2.1
  have hd2 : (sec_m a).det = 1 := isLowUni_det K a.2.1
  rw [sec_mem_int R _ hd1, sec_mem_int R _ hd2, sec_lowJ_m, blkM_isInt]
  constructor
  · rintro ⟨hA, -, ha, -⟩
    refine ⟨hA, fun j => ?_⟩
    have hmem := (sec_mem_int R a hd2).2 hA
    have hinvI : IsInt R (sec_m a)⁻¹ := by
      have h2 := hmem.2
      rwa [Matrix.coe_units_inv] at h2
    have hinv : sec_m a * (sec_m a)⁻¹ = 1 := by
      rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ρ = (ρ ᵥ* sec_m a) ᵥ* (sec_m a)⁻¹ := by
      rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
    rw [e]
    exact sec_vecMul_int R hinvI ha j
  · rintro ⟨hA, hρ⟩
    exact ⟨hA, fun i => R.zero_mem, fun j => sec_vecMul_int R hA hρ j, R.one_mem⟩
end Formalism.FourierDecayAlt.P.A5x8
