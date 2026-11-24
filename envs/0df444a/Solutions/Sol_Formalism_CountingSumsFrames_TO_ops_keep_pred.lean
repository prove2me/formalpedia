-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ops_keep_pred
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:00.971066+00:00
-- url     : https://prove2.me/submissions/d0a2ea9b-d302-4827-938c-405255eaeffd

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_ops_keep_supp


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
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (S : Set σ) (P : σ → Prop) (hS : ∀ v ∈ S, P v) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ FockB.Ops S) (g : MvPolynomial σ k) (hg : ∀ m ∈ g.support, ∀ v, m v ≠ 0 → P v) :
    ∀ m ∈ (T g).support, ∀ v, m v ≠ 0 → P v := by
  have h1 := ops_keep_supp S {m : σ →₀ ℕ | ∀ v, m v ≠ 0 → P v} (fun m m' h hm v hv => by
    by_cases hvS : v ∈ S
    · exact hS v hvS
    · exact hm v (by rw [h v hvS]; exact hv)) hT g (by
      rw [mem_restrictSupport_iff]
      intro m hm
      exact hg m (Finset.mem_coe.mp hm))
  rw [mem_restrictSupport_iff] at h1
  intro m hm
  exact h1 (Finset.mem_coe.mpr hm)
end Formalism.CountingSumsFrames.TO
