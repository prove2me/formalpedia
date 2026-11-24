-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_putL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:24.658045+00:00
-- url     : https://prove2.me/submissions/b113ab80-f4cb-43fb-83c9-5e45ecc1f686

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_rename
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_one

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
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (i : L) (α : L × Fin r →₀ ℕ) {a : ℝ}
    {Q : MvPolynomial (Fin r) K} (hQ : cge v a Q) : cge v a (putL i α Q) := by
  rw [putL_eq_monomial_mul_rename]
  have h := cge_mul v (cge_monomial v (offE i α) (vge_one v))
    (cge_rename v (fun a : Fin r => (i, a)) (fun x y hxy => by simpa using hxy) hQ)
  rwa [zero_add] at h
end Formalism.MainNotions.PlaneGram
