-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.t_RowFromClasses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:16.918005+00:00
-- url     : https://prove2.me/submissions/6a7db65d-a3fc-48fb-8b84-35f1be0d7771

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
theorem _root_.solution : Formalism.FourierDecayAlt.PN.RowFromClasses := by
  intro hCS τ Rw I H H₁ _ _ _ _ _ _ X E _ r Cl Nu N hAbs hCl
  obtain ⟨_, hvec, hG⟩ := hAbs
  set v : τ → H₁ := X.ngSet.indicator X.vec with hv
  have hvs : Summable (fun i => ‖v i‖) := by
    have : (fun i => ‖v i‖) = X.ngSet.indicator (fun i => ‖X.vec i‖) := by
      funext i; simp [hv, norm_indicator_eq_indicator_norm]
    rw [this]; exact hvec.indicator _
  obtain ⟨hsum, heq⟩ := hCS τ Cl H₁ v N.cls hvs
  have key : ∀ c, ∑' i, ({i | N.cls i = c} : Set τ).indicator v i =
      ∑' x : Pts E r × Nu, grp X N c x.1 x.2 := by
    intro c
    set u : τ → H₁ := ({i | N.cls i = c} : Set τ).indicator v with hu
    have hus : Summable u := by
      have h1 : Summable v := hvs.of_norm
      exact h1.indicator _
    have h2 := (hus.hasSum.tsum_fiberwise (fun t => (N.pt t, N.nml t))).tsum_eq
    rw [← h2]
    apply tsum_congr
    intro x
    rw [_root_.tsum_subtype]
    unfold grp
    apply tsum_congr
    intro t
    by_cases h1 : t ∈ X.ngSet <;> by_cases h2 : N.cls t = c <;> by_cases h3 : N.pt t = x.1 <;>
      by_cases h4 : N.nml t = x.2 <;>
      simp [hu, hv, Set.indicator, h1, h2, h3, h4, Prod.ext_iff]
  have hfun : (fun c => ‖∑' i, ({i | N.cls i = c} : Set τ).indicator v i‖ ^ 2) =
      (fun c => ‖∑' x : Pts E r × Nu, grp X N c x.1 x.2‖ ^ 2) := by
    funext c; rw [key c]
  refine ⟨hfun ▸ hsum, ?_⟩
  rw [← hfun, ← heq]
  unfold PB.Terms.pairSum
  congr 1
  apply tsum_congr
  intro p
  by_cases h1 : p.1 ∈ X.ngSet
  · by_cases h2 : p.2 ∈ X.ngSet
    · have hiff := hCl p.1 h1 p.2 h2
      by_cases h3 : N.cls p.1 = N.cls p.2
      · have h4 := hiff.2 h3
        have hm : p ∈ X.one X.ngSet := ⟨⟨h1, h2, h4.1⟩, h4.2⟩
        simp [Set.indicator, hm, h3, hv, h1, h2]
      · have hm : p ∉ X.one X.ngSet := fun hm => h3 (hiff.1 ⟨hm.1.2.2, hm.2⟩)
        simp [Set.indicator, hm, h3]
    · have hm : p ∉ X.one X.ngSet := fun hm => h2 hm.1.2.1
      simp [Set.indicator, hm, hv, h2]
  · have hm : p ∉ X.one X.ngSet := fun hm => h1 hm.1.1
    simp [Set.indicator, hm, hv, h1]
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
