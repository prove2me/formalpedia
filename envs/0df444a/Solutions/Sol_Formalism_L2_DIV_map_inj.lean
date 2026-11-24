-- Prove2me | solution 1 for Formalism.L2.DIV.map_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:55:29.245659+00:00
-- url     : https://prove2.me/submissions/ee90845f-9fd9-4337-8aa0-de6cc8e018c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_exists_left_inv
import Theorems.Thm_Formalism_L2_DIV_inj_of_left_inv
import Theorems.Thm_P2M_Formalism_L2_DIV_map_one__d0eedca16a10

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
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (h : Function.Injective E.mulVec) : Function.Injective (E.map σ).mulVec := by
  obtain ⟨L, hL⟩ := exists_left_inv E h
  apply inj_of_left_inv (L := L.map σ)
  rw [← Matrix.map_mul, hL, map_one']
end Formalism.L2.DIV
