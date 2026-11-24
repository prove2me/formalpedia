-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.forms_devissage_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:50.292719+00:00
-- url     : https://prove2.me/submissions/5d7b2c04-82a7-418a-9b54-e73104b0a4d8

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : FormsDevissage := by
  intro O _ A _ _ G _ Γ K jK T _ V _ _ _ _ _ S D₀ D E hN hA hD0 hDE hstep f hf
  let Φ : Submodule A V → Submodule O (V ⧸ D₀) := fun F => (F.restrictScalars O).map D₀.mkQ
  have hΦmono : ∀ F1 F2 : Submodule A V, F1 ≤ F2 → Φ F1 ≤ Φ F2 := fun F1 F2 h =>
    Submodule.map_mono (fun x hx => h hx)
  have hΦ : ∀ F1 F2 : Submodule A V, D ≤ F1 → Φ F2 ≤ Φ F1 → F2 ≤ F1 := by
    intro F1 F2 h1 h x hx
    obtain ⟨y, hy, hxy⟩ := h (Submodule.mem_map_of_mem (f := D₀.mkQ) (show x ∈ F2.restrictScalars O from hx))
    have h2 : y - x ∈ D₀ := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      exact sub_eq_zero.mpr hxy
    have h3 : y - x ∈ F1 := h1 (hD0 h2)
    have h4 : x = y - (y - x) := by abel
    rw [h4]
    exact F1.sub_mem hy h3
  let PP : Set (Submodule A V) := {F | D ≤ F ∧ F ≤ E ∧
    ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F}
  have hE : E ∈ PP := ⟨hDE, le_rfl, 1, S.one_mem, by simpa using hf⟩
  obtain ⟨_, ⟨F, hF, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (Φ '' PP) ⟨_, E, hE, rfl⟩
  obtain ⟨hDF, hFE, s, hs, hsf⟩ := hF
  by_cases hEq : F ≤ D
  · exact ⟨s, hs, fun g => hEq (hsf g)⟩
  · exfalso
    have hlt : D < F := lt_of_le_not_ge hDF hEq
    have hNA : IsNoetherian A V := isNoetherian_of_tower O hN
    obtain ⟨F0, ⟨hDF0, hF0F⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr hNA
      {F0 : Submodule A V | D ≤ F0 ∧ F0 < F} ⟨D, le_rfl, hlt⟩
    have hcov : F0 ⋖ F := ⟨hF0F, fun c h1 h2 => hmax c ⟨hDF0.trans h1.le, h2⟩ h1⟩
    obtain ⟨s', hs', hs'f⟩ := hstep F0 F hDF0 hcov hFE (s • f) hsf
    have hF0 : F0 ∈ PP := ⟨hDF0, hF0F.le.trans hFE, s' * s, S.mul_mem hs' hs, by
      intro g
      rw [mul_smul]
      exact hs'f g⟩
    apply hmin (Φ F0) ⟨F0, hF0, rfl⟩
    refine lt_of_le_not_ge (hΦmono _ _ hF0F.le) fun h => ?_
    exact absurd (hΦ F0 F hDF0 h) (not_le_of_gt hF0F)
end Formalism.CohomologicalDescent.DepthNonnegative
