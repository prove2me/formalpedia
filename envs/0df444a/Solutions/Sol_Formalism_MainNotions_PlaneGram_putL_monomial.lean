-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.putL_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:24.760865+00:00
-- url     : https://prove2.me/submissions/1b1a858d-ce77-479b-946a-71835c3e5ad7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
section Gen
variable {σ : Type} [Fintype σ]
end Gen
section Letter
variable {L : Type} [DecidableEq L] {r : ℕ}
end Letter
section Der
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
end Der
section App
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
private theorem putL_eq_monomial_mul_rename (i : L) (α : L × Fin r →₀ ℕ) (Q : MvPolynomial (Fin r) K) :
    putL i α Q = monomial (offE i α) (1 : K) * rename (fun a : Fin r => (i, a)) Q := by
  simp only [putL, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
variable {I : Type} [Fintype I]
end App
section AppL
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]
end AppL
namespace TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
end TwistData
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (i : L) (α : L × Fin r →₀ ℕ) (η : Fin r →₀ ℕ) (c : K) :
    putL i α (monomial η c) = monomial (offE i α + onLetter i η) c := by
  rw [putL_eq_monomial_mul_rename, rename_monomial, monomial_mul, one_mul, onLetter]
end Formalism.MainNotions.PlaneGram
