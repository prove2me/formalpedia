-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.pderiv_xv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:41.133889+00:00
-- url     : https://prove2.me/submissions/6ceae21f-4aea-4c93-8e75-09e003c5887c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_not
import Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_Z

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (p : Fin (D + 1) × Fin m) :
    pderiv q (xv (Ω := Ω) j₀ p) = if p = q.1 then 1 else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [xv_of_Z hp, map_zero, if_neg hne]
  · rw [xv_of_not hp, pderiv_X, Pi.single_apply]
    by_cases h : p = q.1
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) = q := Subtype.ext h
      rw [if_pos e, if_pos h]
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) ≠ q :=
        fun e => h (congrArg Subtype.val e)
      rw [if_neg e, if_neg h]
end Formalism.L2.Pj.GenSect
