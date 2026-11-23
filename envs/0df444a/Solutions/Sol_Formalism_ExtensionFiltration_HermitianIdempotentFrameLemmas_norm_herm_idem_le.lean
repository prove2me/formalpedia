-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.norm_herm_idem_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:46.394419+00:00
-- url     : https://prove2.me/submissions/a9529ea0-6b9f-4e0f-a2b9-e0b3914bcfbc

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (R : Matrix ι ι ℂ) (h1 : R.IsHermitian) (h2 : R * R = R)
    (z : EuclideanSpace ℂ ι) : ‖Matrix.toEuclideanLin R z‖ ≤ ‖z‖ := by
  have hs : (Matrix.toEuclideanLin R).IsSymmetric := (Matrix.isHermitian_iff_isSymmetric).1 h1
  have hTT : ∀ w, Matrix.toEuclideanLin R (Matrix.toEuclideanLin R w) = Matrix.toEuclideanLin R w := by
    intro w
    rw [Matrix.toEuclideanLin_eq_toLin, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h2]
  set y := Matrix.toEuclideanLin R z with hy
  have h3 : @inner ℂ _ _ y y = @inner ℂ _ _ z y := by
    have h4 := hs z y
    rw [hy, hTT z] at h4
    rw [hy]
    exact h4
  have h5 : ‖y‖ ^ 2 ≤ ‖z‖ * ‖y‖ := by
    have h6 := re_inner_le_norm (𝕜 := ℂ) z y
    have h7 : RCLike.re (@inner ℂ _ _ y y) = ‖y‖ ^ 2 := inner_self_eq_norm_sq y
    rw [h3] at h7
    linarith
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
