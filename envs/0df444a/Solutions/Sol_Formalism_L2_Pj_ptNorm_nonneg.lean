-- Prove2me | solution 1 for Formalism.L2.Pj.ptNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:05.417515+00:00
-- url     : https://prove2.me/submissions/09f5d399-0347-423b-87df-976e6aab409a

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
theorem _root_.solution (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) : 0 ≤ ptNorm pts mapR σ fnorm e f y :=
  mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => pow_nonneg (inv_nonneg.2 (abs_nonneg _)) _)
end Formalism.L2.Pj
