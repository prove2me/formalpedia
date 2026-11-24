-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.goodE_splitE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:53:02.313357+00:00
-- url     : https://prove2.me/submissions/bb4e2105-4f1d-4672-acc0-74c31b46f4d2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_ldeg_congr__7f80ac31fcf2
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mlab
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mtp

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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {p : ℕ} (hp : 0 < p) {ζ : D.EM} (hw : ∀ t a, ζ (D.mw t, a) = 0)
    (hpost : ∀ j, D.PostE j ζ) : D.GoodE p (D.splitE p ζ) := by
  have hP : ∀ t, 0 < D.P p t := fun t => by
    unfold P
    exact pow_pos hp _
  refine ⟨fun t a => ?_, fun j m hm a => ?_, fun b => ?_, fun t => ?_, fun t => ?_⟩
  · rw [splitE_mlab]
    exact Nat.mod_lt _ (hP t)
  · rw [splitE_mtp]
    exact (hpost j).2.2.2 m hm a
  · rw [D.ldeg_congr' (fun a => D.splitE_mb p ζ b a)]
    exact (hpost (D.seg b)).1 b rfl
  · obtain ⟨j, m⟩ := t
    have e1 : ldeg (D.splitE p ζ) (D.mlab (j, m)) + D.P p (j, m) * ldeg (D.splitE p ζ) (D.mw (j, m))
        = ldeg ζ (D.mlab (j, m)) := by
      unfold ldeg
      simp only [splitE_mlab, splitE_mw, hw, zero_add]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Nat.mod_add_div _ _
    rw [e1, D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]
    exact (hpost j).2.1 m
  · obtain ⟨j, m⟩ := t
    rw [D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]
    exact (hpost j).2.2.1 m
end Formalism.MainNotions.PlaneGram.TwistData
