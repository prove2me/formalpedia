-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationWordBounds.ck_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:29:43.440852+00:00
-- url     : https://prove2.me/submissions/58a45b4f-0045-40a6-a2ac-790cff6150f9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LetterPairStep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dLR_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChartIntegralLocal_ck_at_of_chart
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChartIntegralLocal_int_chart_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_dLR_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_ckOn_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_ckOn_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_continuous_xiP
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_dLR_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_good_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_isOpen_OmPlus
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_norm_xiP
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Lt_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Mv_co
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_chart_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_chart_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_chart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_co_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_prj_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_zero_mem_dom
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationWordBounds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
variable (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
include hFm hDom1 hDom2
namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds
theorem _root_.solution : Formalism.FourierDecayAlt.Q.CkLev k r 0 m (Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') (JF D F) := by
  classical
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  intro g0 hg0
  have hg0G : g0 ∈ GV k r := hg0.1.1
  have hchart0 : Formalism.FourierDecayAlt.P.Ux10.chart g0 0 = g0 := by
    have h1 : (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) = Formalism.FourierDecayAlt.P.Ux10.co 0 :=
      funext fun i => (Formalism.FourierDecayAlt.P.Ux10.co_zero i).symm
    unfold Formalism.FourierDecayAlt.P.Ux10.chart Formalism.FourierDecayAlt.P.Ux10.kap
    rw [h1, Formalism.FourierDecayAlt.P.Ux10.Mv_co, Formalism.FourierDecayAlt.P.Ux10.prj_zero]
    simp
  have hcont : ContinuousAt (Formalism.FourierDecayAlt.P.Ux10.chart g0) 0 :=
    (Formalism.FourierDecayAlt.P.Ux10.chart_diff g0 Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom).continuousAt
  have hV : Formalism.FourierDecayAlt.P.Ux10.Dom k r ∩ Formalism.FourierDecayAlt.P.Ux10.chart g0 ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' ∈
      𝓝 (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) :=
    Filter.inter_mem (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom)
      (hcont.preimage_mem_nhds ((isOpen_OmPlus _ _).mem_nhds (by rw [hchart0]; exact hg0.2)))
  obtain ⟨δ1, hδ1, hsub⟩ := Metric.mem_nhds_iff.1 hV
  set δ := δ1 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hclb : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Metric.ball 0 δ1 :=
    Metric.closedBall_subset_ball (by rw [hδ]; linarith)
  have hcl : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Formalism.FourierDecayAlt.P.Ux10.Dom k r :=
    fun Y hY => (hsub (hclb hY)).1
  set K := Formalism.FourierDecayAlt.P.Ux10.chart g0 '' Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn ((Formalism.FourierDecayAlt.P.Ux10.chart_cd g0).continuousOn.mono hcl)
  have hKOm : K ⊆ Om k r D.z D.z' := by
    rintro _ ⟨Y, hY, rfl⟩
    exact (⟨Formalism.FourierDecayAlt.P.Ux10.chart_mem hg0G (hcl hY), (hsub (hclb hY)).2⟩ :
      Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')
  have hKG : K ⊆ GV k r := fun x hx => (show x ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' from hKOm hx).1
  have hmemK : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ K :=
    fun Y hY => ⟨Y, Metric.ball_subset_closedBall hY, rfl⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 K hK hKOm
  set WS : Set (List (Mat k r) × List (Mat k r)) :=
    (fun w : List (Formalism.FourierDecayAlt.P.Ux10.J k r) => (w.map Formalism.FourierDecayAlt.P.Ux10.Lt, ([] : List (Mat k r)))) ''
      {w | w.length ≤ m} with hWSdef
  have hWS : WS.Countable := (Set.to_countable _).image _
  have hunit : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), ∀ X ∈ w.map Formalism.FourierDecayAlt.P.Ux10.Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Formalism.FourierDecayAlt.P.Ux10.Lt_unit i
  have hWSl : ∀ uv ∈ WS, (∀ Y ∈ uv.1, unitLie k r Y) ∧ (∀ Y ∈ uv.2, unitLie k r Y) ∧
      uv.1.length + uv.2.length ≤ m := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hunit w, by simp, by simpa using hw⟩
  have good := good_set D hFm hK hKG hWS hWSl bd fun uv huv g' hg' =>
    hbd uv.1 uv.2 (hWSl uv huv).1 (hWSl uv huv).2.1 (hWSl uv huv).2.2 g' hg'
  set P0 : Set (SS k r) := {p | D.inSS p ∧ ∀ uv ∈ WS, ∀ g' ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g'‖ ≤ bd p} with hP0
  have goodae : ∀ᵐ p ∂D.μSS, p ∈ P0 := good
  set hK' : SS k r → Mat k r → (Wq →L[ℂ] Wp) := fun p => if p ∈ P0 then rho D p F else fun _ => 0 with hK'def
  have hsel : ∀ p (u' v' : List (Mat k r)),
      dLR u' v' (hK' p) = if p ∈ P0 then dLR u' v' (rho D p F) else fun _ => 0 := by
    intro p u' v'
    by_cases hp : p ∈ P0
    · simp only [hK'def, if_pos hp]
    · simp only [hK'def, if_neg hp, dLR_zero]
  have hAL := int_chart_loc (xiP D) (fun p => norm_xiP D p) (continuous_xiP D).aestronglyMeasurable hK' m
    (fun p => by
      by_cases hp : p ∈ P0
      · simp only [hK'def, if_pos hp]; exact ckOn_rho D hp.1 hFm
      · simp only [hK'def, if_neg hp]; exact ckOn_zero _)
    hg0G hδp hcl
    (fun w hw Y hY => by
      refine (hDom1 (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hunit w) (by simp) (by simpa using hw) _
        (hKOm (hmemK Y hY))).congr ?_
      filter_upwards [goodae] with p hp
      rw [hsel, if_pos hp, dLR_rho D hp.1])
    (fun p => ‖bd p‖) hbdI.norm
    (fun w hw Y hY p => by
      rw [hsel]
      by_cases hp : p ∈ P0
      · rw [if_pos hp]; exact (hp.2 _ ⟨w, hw, rfl⟩ _ (hmemK Y hY)).trans (Real.le_norm_self _)
      · rw [if_neg hp, norm_zero]; exact norm_nonneg _)
  have hAL' : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => JF D F (Formalism.FourierDecayAlt.P.Ux10.chart g0 Y))
      (Metric.ball 0 δ) := by
    refine hAL.congr fun Y _ => ?_
    show ∫ p, xiP D p • rho D p F _ ∂D.μSS = _
    refine integral_congr_ae ?_
    filter_upwards [goodae] with p hp
    simp only [hK'def, if_pos hp]
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := ck_at_of_chart hg0G hδp hAL'
  exact ⟨U, F', hU, hgU, hF', fun g hg hgl => hUF g hg hgl.1⟩
end Formalism.FourierDecayAlt.P.WeakDominationWordBounds
