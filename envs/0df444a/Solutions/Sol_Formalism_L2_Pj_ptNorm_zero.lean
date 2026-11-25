-- Prove2me | solution 1 for Formalism.L2.Pj.ptNorm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:40.494606+00:00
-- url     : https://prove2.me/submissions/807cf864-4606-4e6a-9245-dcc0797b3347

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Theorems.Thm_Formalism_L2_Pj_evalAt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPolynomial
variable {K : Type} [Field K]
variable {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
namespace Formalism.L2.Pj
theorem _root_.solution (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (y : pts (CAt σ)) :
    ptNorm pts mapR σ fnorm e 0 y = 0 := by
  unfold ptNorm; rw [evalAt_zero]
  exact mul_eq_zero_of_left (norm_zero (E := ℂ)) _
end Formalism.L2.Pj
