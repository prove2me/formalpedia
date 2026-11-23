-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.t_ClassCS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:00.77414+00:00
-- url     : https://prove2.me/submissions/4d1990a1-8781-47a5-99c3-91c888b1adf8

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_C_fin_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
theorem _root_.solution : Formalism.FourierDecayAlt.PN.ClassCS := by
  unfold Formalism.FourierDecayAlt.PN.ClassCS
  intro hW Cl J V _ U W y Sw M h0 hWp hy h1 h2 Cs
  classical
  let U' : Cl → J → V := fun c j => if Summable (U c) then U c j else 0
  have hU'0 : ∀ c j, U' c j ≠ 0 → U c j ≠ 0 := by
    intro c j h hc
    apply h
    simp [U', hc]
  have hU'n : ∀ c j, ‖U' c j‖ ^ 2 ≤ y c j := by
    intro c j
    by_cases hs : Summable (U c)
    · have e : U' c j = U c j := by simp [U', hs]
      rw [e]
      exact hy c j
    · have e : U' c j = 0 := by simp [U', hs]
      rw [e, norm_zero]
      linarith [hy c j, sq_nonneg ‖U c j‖]
  have hsum : ∀ c, Summable (U' c) := by
    intro c
    by_cases hs : Summable (U c)
    · have e : U' c = U c := by funext j; simp [U', hs]
      rw [e]
      exact hs
    · have e : U' c = fun _ => 0 := by funext j; simp [U', hs]
      rw [e]
      exact summable_zero
  have htsum : ∀ c, ∑' j, U' c j = ∑' j, U c j := by
    intro c
    by_cases hs : Summable (U c)
    · have e : U' c = U c := by funext j; simp [U', hs]
      rw [e]
    · have e : U' c = fun _ => 0 := by funext j; simp [U', hs]
      rw [e, tsum_zero, tsum_eq_zero_of_not_summable hs]
  have hfin := fin_bound hW U' W y Sw M h0 (fun c j h => hWp c j (hU'0 c j h)) hU'n
    (fun c T hT => h1 c T (fun j hj => hU'0 c j (hT j hj)))
    (fun T hT => h2 T (fun x hx => hU'0 _ _ (hT x hx))) Cs
  have hlim : Filter.Tendsto (fun T : Finset J => ∑ c ∈ Cs, ‖∑ j ∈ T, U' c j‖ ^ 2) Filter.atTop
      (nhds (∑ c ∈ Cs, ‖∑' j, U' c j‖ ^ 2)) := by
    refine tendsto_finset_sum Cs (fun c _ => ?_)
    have ht : Filter.Tendsto (fun T : Finset J => ∑ j ∈ T, U' c j) Filter.atTop
        (nhds (∑' j, U' c j)) := (hsum c).hasSum
    exact ht.norm.pow 2
  have hle := le_of_tendsto' hlim hfin
  simpa only [htsum] using hle
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
