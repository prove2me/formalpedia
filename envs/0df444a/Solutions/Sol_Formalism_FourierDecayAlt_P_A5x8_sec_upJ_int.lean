-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_upJ_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:38.656123+00:00
-- url     : https://prove2.me/submissions/7b61f741-a0a0-46ce-9206-dd007cf10242

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mulVec_int

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
theorem _root_.solution (h : Point K) (c : Kˣ) (b : upUniG K h.1.sum) (ρ : Fin h.1.sum → K) :
    sec_upJ h c b ρ ∈ intSub R (upUniG K (addBlock h 1 c).1.sum) ↔
      b ∈ intSub R (upUniG K h.1.sum) ∧ ∀ j, ρ j ∈ R := by
  have hd1 : (sec_m (sec_upJ h c b ρ)).det = 1 := isUpUni_det K (sec_upJ h c b ρ).2
  have hd2 : (sec_m b).det = 1 := isUpUni_det K b.2
  rw [sec_mem_int R _ hd1, sec_mem_int R _ hd2, sec_upJ_m, blkM_isInt]
  constructor
  · rintro ⟨hA, hb, -, -⟩
    refine ⟨hA, fun j => ?_⟩
    have hmem := (sec_mem_int R b hd2).2 hA
    have hinvI : IsInt R (sec_m b)⁻¹ := by
      have h2 := hmem.2
      rwa [Matrix.coe_units_inv] at h2
    have hinv : (sec_m b)⁻¹ * sec_m b = 1 := by
      rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ρ = (sec_m b)⁻¹ *ᵥ (sec_m b *ᵥ ρ) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [e]
    exact sec_mulVec_int R hinvI hb j
  · rintro ⟨hA, hρ⟩
    exact ⟨hA, fun i => sec_mulVec_int R hA hρ i, fun j => R.zero_mem, R.one_mem⟩
end Formalism.FourierDecayAlt.P.A5x8
