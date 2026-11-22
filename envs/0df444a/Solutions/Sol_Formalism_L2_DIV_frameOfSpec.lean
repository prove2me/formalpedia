-- Prove2me | solution 1 for Formalism.L2.DIV.frameOfSpec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:09.825812+00:00
-- url     : https://prove2.me/submissions/1598ef15-4d61-43e8-aa5c-7edaabfe4bc0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : FrameOfSpec := by
  intro n A hA
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A := hA.posSemidef.nonneg
  have hs : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have hdet : IsUnit (CFC.sqrt A).det := by
    have h1 : A.det ≠ 0 := hA.det_pos.ne'
    rw [← hs, Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  have hH : (CFC.sqrt A)ᴴ = CFC.sqrt A := by
    have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  rw [metOf, frameOf, Matrix.nonsing_inv_nonsing_inv _ hdet, hH, hs]
end Formalism.L2.DIV
