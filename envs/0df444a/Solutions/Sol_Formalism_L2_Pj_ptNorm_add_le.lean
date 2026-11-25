-- Prove2me | solution 1 for Formalism.L2.Pj.ptNorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:29.330894+00:00
-- url     : https://prove2.me/submissions/88027ae2-127a-47c1-8a75-d0c706c341a9

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
theorem _root_.solution (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f g : Rules pts)
    (y : pts (CAt σ)) :
    ptNorm pts mapR σ fnorm e (f + g) y ≤ ptNorm pts mapR σ fnorm e f y + ptNorm pts mapR σ fnorm e g y := by
  unfold ptNorm
  rw [evalAt_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
    (Finset.prod_nonneg fun _ _ => pow_nonneg (inv_nonneg.2 (abs_nonneg _)) _)
end Formalism.L2.Pj
