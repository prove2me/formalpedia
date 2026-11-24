-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.hb_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:16.248897+00:00
-- url     : https://prove2.me/submissions/463ea810-61e5-43c8-b9d3-092f05585463

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_mem_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (t : ℝ) (ht : t ≠ 0) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' (((t ^ (1 + r') : ℝ) : ℂ) • (aDil k r' t *ᵥ y)) (t ^ (2 * (1 + r')) * s) =
      ((t ^ (1 + r') : ℝ) : ℂ) ^ 2 * hb k r' y s := by
  unfold hb
  rw [herm_smul_left, herm_smul_right, herm_UH (dilation_mem_group k r' t ht), Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul, pow_mul' t 2 (1 + r')]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.B2x7
