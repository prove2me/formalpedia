-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.border_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:33.55283+00:00
-- url     : https://prove2.me/submissions/2b6cb6bc-d932-49e5-95e4-1945fb00d01e

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_up_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_mk_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {r : ℕ} {U : Matrix (Fin r) (Fin r) A} (hU : IsUpUni U) (v : Fin r → A) :
    IsUpUni (border U v 0 1) := by
  refine mk_up ?_ ?_
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h; exact absurd h (lt_irrefl _)
    · intro _; simp
    · intro h; exact absurd h (not_lt.mpr (Fin.le_last _))
    · intro h; rw [border_cc]; exact up_apply hU (by simpa using h)
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · rw [border_cc]; exact hU.2 i
end Formalism.FourierDecayAlt.P.S3x7
