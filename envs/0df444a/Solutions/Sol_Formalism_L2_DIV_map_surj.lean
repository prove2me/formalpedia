-- Prove2me | solution 1 for Formalism.L2.DIV.map_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:28.794799+00:00
-- url     : https://prove2.me/submissions/2039329e-d6d7-4df5-8472-4a0842754a5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
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
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (P : Matrix (Fin d) (Fin n) K)
    (h : Function.Surjective P.mulVec) : Function.Surjective (P.map σ).mulVec := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  exact ⟨R.map σ, by rw [← Matrix.map_mul, hR, map_one']⟩
end Formalism.L2.DIV
