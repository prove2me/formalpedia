-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.border_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:31.492197+00:00
-- url     : https://prove2.me/submissions/e51dfa54-723e-4828-b7b1-ada43137c0f6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_low_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_mk_low
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
theorem _root_.solution {r : ℕ} {L : Matrix (Fin r) (Fin r) A} (hL : IsLowUni L) (u : Fin r → A) :
    IsLowUni (border L 0 u 1) := by
  refine mk_low ?_ ?_
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h; exact absurd h (lt_irrefl _)
    · intro h; exact absurd h (not_lt.mpr (Fin.le_last _))
    · intro _; simp
    · intro h; rw [border_cc]; exact low_apply hL (by simpa using h)
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · rw [border_cc]; exact hL.2 i
end Formalism.FourierDecayAlt.P.S3x7
