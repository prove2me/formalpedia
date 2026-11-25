-- Prove2me | solution 1 for Formalism.L2.Pj.ptNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:32.951943+00:00
-- url     : https://prove2.me/submissions/d9acfed4-64bc-4907-b59b-8e0ba36f878e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt

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
theorem _root_.solution (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (a : K) (f : Rules pts)
    (y : pts (CAt σ)) :
    ptNorm pts mapR σ fnorm e (a • f) y = ‖σ a‖ * ptNorm pts mapR σ fnorm e f y := by
  unfold ptNorm
  rw [evalAt_smul, ← mul_assoc]
  congr 1
  unfold cabs
  exact norm_mul (σ a) _
end Formalism.L2.Pj
