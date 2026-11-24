-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.subX_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:37.397281+00:00
-- url     : https://prove2.me/submissions/4cb82185-8e1a-4124-85cc-a8357103814c

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
variable (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (x : L × Fin r) (hx : ¬ out x.1) :
    subX sg S A B x ∈ supported R {y : L × Fin r | ¬ out y.1} := by
  have hX : ∀ b, (X (x.1, b) : MvPolynomial (L × Fin r) R) ∈ supported R {y : L × Fin r | ¬ out y.1} := by
    intro b
    rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨(x.1, b), hx, rfl⟩
  have hCm : ∀ a : R, (C a : MvPolynomial (L × Fin r) R) ∈ supported R {y : L × Fin r | ¬ out y.1} :=
    fun a => Subalgebra.algebraMap_mem _ a
  unfold subX
  split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hCm _) (hX b)
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hCm _) (hX b)
  · exact hX x.2
end Formalism.MainNotions.PlaneGram
