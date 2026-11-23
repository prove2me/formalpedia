-- Prove2me | solution 1 for Formalism.L2.DIV.sum_map_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:29.87838+00:00
-- url     : https://prove2.me/submissions/59fc4f97-26c1-4bae-be4f-5f253f93c73b

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
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ix : Type} [Fintype Ix]
namespace Formalism.L2.DIV
theorem _root_.solution (pr : Ix → Matrix (Fin n) (Fin n) K) (hsum : ∑ p, pr p = 1) (σ : K →+* ℂ) :
    ∑ p, (pr p).map σ = 1 := by
  have := congrArg σ.mapMatrix hsum
  simpa [map_sum, RingHom.mapMatrix_apply] using this
end Formalism.L2.DIV
