-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:18:10.659748+00:00
-- url     : https://prove2.me/submissions/d1c07c03-b20e-4e15-b986-0db3d989e30f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_one

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
variable {sg S}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type} (s : Finset ι) (θ : ι → ℝ) (f : ι → MvPolynomial (L × Fin r) K)
    (h : ∀ i ∈ s, vala sg S (θ i) (f i)) : vala sg S (∑ i ∈ s, θ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vala_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact vala_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.MainNotions.PlaneGram
