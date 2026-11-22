-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.substS_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:21.50172+00:00
-- url     : https://prove2.me/submissions/028df1e7-b698-43fe-9443-728b7ee85722

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (α : L × Fin r →₀ ℕ) (c : K) :
    substS ι sg S A B (monomial α c) = C (ι c) * α.prod fun x k => subX sg S A B x ^ k := by
  unfold substS
  rw [eval₂Hom_monomial]
  rfl
end Formalism.MainNotions.PlaneGram
