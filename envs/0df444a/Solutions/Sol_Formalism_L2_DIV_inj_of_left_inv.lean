-- Prove2me | solution 1 for Formalism.L2.DIV.inj_of_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:39.156065+00:00
-- url     : https://prove2.me/submissions/b8328e9c-87ec-4af0-961f-a1761ce0b67f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {F : Type} [Field F] {n d : ℕ} {C : Matrix (Fin n) (Fin d) F}
    {L : Matrix (Fin d) (Fin n) F} (h : L * C = 1) : Function.Injective C.mulVec := by
  intro x y hxy
  have := congrArg L.mulVec hxy
  simpa [Matrix.mulVec_mulVec, h] using this
end Formalism.L2.DIV
