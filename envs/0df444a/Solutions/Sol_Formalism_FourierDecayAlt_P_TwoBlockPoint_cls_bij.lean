-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.cls_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:34.407884+00:00
-- url     : https://prove2.me/submissions/7b82cad0-4847-4779-9035-079d8b683691

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cls_leftInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {ι κ : Type} (L L' : Matrix ι κ K → Matrix ι κ K)
    (hadd : ∀ U V, L (U + V) = L U + L V) (hadd' : ∀ U V, L' (U + V) = L' U + L' V)
    (hint : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L V i j ∈ R)
    (hint' : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L' V i j ∈ R)
    (hinv : ∀ U, L' (L U) = U) (hinv' : ∀ U, L (L' U) = U) :
    Function.Bijective (fun x : Matrix ι κ (KR R) => clsM R (L (outM R x))) := by
  refine ⟨fun x₁ x₂ e => ?_, fun y => ⟨clsM R (L' (outM R y)), cls_leftInv R L' L hadd hint hinv' y⟩⟩
  have e' : clsM R (L (outM R x₁)) = clsM R (L (outM R x₂)) := e
  exact (cls_leftInv R L L' hadd' hint' hinv x₁).symm.trans
    ((congrArg (fun y => clsM R (L' (outM R y))) e').trans (cls_leftInv R L L' hadd' hint' hinv x₂))
end Formalism.FourierDecayAlt.P.TwoBlockPoint
