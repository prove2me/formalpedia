-- Prove2me | solution 1 for Formalism.L2.DIV.quotRestrPosDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:55.249792+00:00
-- url     : https://prove2.me/submissions/07383af8-7ada-49ad-a306-e56c3bfbdb60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
import Theorems.Thm_Formalism_L2_DIV_inj_of_left_inv

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
theorem _root_.solution : QuotRestrPosDef := by
  intro n d A hA
  refine ⟨fun P hP => ?_, fun C hC => hA.conjTranspose_mul_mul_same hC⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hP
  have hinj : Function.Injective (Pᴴ).mulVec := by
    apply inj_of_left_inv (L := Rᴴ)
    rw [← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one]
  have h1 := hA.inv.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_conjTranspose] at h1
  exact h1.inv
end Formalism.L2.DIV
