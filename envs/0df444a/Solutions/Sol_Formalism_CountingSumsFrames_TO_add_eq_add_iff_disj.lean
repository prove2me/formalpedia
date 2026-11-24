-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.add_eq_add_iff_disj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:02.401663+00:00
-- url     : https://prove2.me/submissions/37098424-c3bd-4281-a166-d34ff6813e91

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_frst_of
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_of
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_TO_ltr_of__5656358b1af2
import Theorems.Thm_Formalism_CountingSumsFrames_TO_frst_add
import Theorems.Thm_Formalism_CountingSumsFrames_TO_ltr_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (j0 : ℕ) (a b m m' : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hb : ∀ v, b v ≠ 0 → fsj N r j0 v) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) : a + m = b + m' ↔ a = b ∧ m = m' := by
  constructor
  · intro h
    have h1 := congrArg (frst (fsj N r j0)) h
    have h2 := congrArg (ltr (fsj N r j0)) h
    rw [frst_add, frst_add, frst_of _ ha, frst_of _ hb, frst_of' _ hm, frst_of' _ hm', add_zero, add_zero] at h1
    rw [ltr_add, ltr_add, ltr_of _ ha, ltr_of _ hb, ltr_of' _ hm, ltr_of' _ hm', zero_add, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl
end Formalism.CountingSumsFrames.TO
