-- Prove2me | solution 1 for Formalism.L2.DIV.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:52:06.084036+00:00
-- url     : https://prove2.me/submissions/c924e4ac-71e8-4cfd-ace1-9a4d55dc8e0d

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_L2_DIV_isAlgebraicQb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (ι : Qb →+* ℂ) (LL : Fld) (σ : CoF ι LL →+* ℂ) :
    ∃ τ : Qb →+* ℂ, ∀ x : CoF ι LL, τ (CoF.val ι LL x) = σ x := by
  have := isAlgebraicQb LL
  let f : LL →ₐ[ℚ] ℂ := RingHom.toRatAlgHom (R := LL) σ
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := LL) (M := ℂ) (E := Qb) f
  refine ⟨φ.toRingHom, fun x => ?_⟩
  exact DFunLike.congr_fun hφ x
end Formalism.L2.DIV
