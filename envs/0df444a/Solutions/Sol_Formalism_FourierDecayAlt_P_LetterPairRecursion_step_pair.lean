-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LetterPairRecursion.step_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:47:03.335989+00:00
-- url     : https://prove2.me/submissions/566053c7-2c7a-4076-b4d0-e7c88c607e4e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LetterPairStep
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dLR_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChartIntegralLocal_step_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_dLR_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_ckOn_dLR_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_ckOn_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_continuous_xiP
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_curve_ball
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_cv_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_dLR_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_good_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_norm_xiP


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LetterPairRecursion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
namespace Formalism.FourierDecayAlt.P.LetterPairRecursion
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
    (b : Bool) {X : Mat k r} (hX : unitLie k r X) {u v u2 v2 : List (Mat k r)}
    (hu : ∀ Y ∈ u, unitLie k r Y) (hv : ∀ Y ∈ v, unitLie k r Y) (hu2 : ∀ Y ∈ u2, unitLie k r Y)
    (hv2 : ∀ Y ∈ v2, unitLie k r Y) (hl2 : u2.length + v2.length ≤ m)
    (hl : u.length + v.length + 1 ≤ u2.length + v2.length)
    (hdl : ∀ f : Mat k r → (Wq →L[ℂ] Wp), dLR u2 v2 f = op b X (dLR u v f))
    (IH : ∀ g ∈ Om k r D.z D.z', dLR u v (JF D F) g = ∫ p, xiP D p • dLR u v (rho D p F) g ∂D.μSS) :
    ∀ g ∈ Om k r D.z D.z', dLR u2 v2 (JF D F) g = ∫ p, xiP D p • dLR u2 v2 (rho D p F) g ∂D.μSS := by
  intro g hg
  have hgG : g ∈ GV k r := hg.1
  have hXL : inLie k r X := hX.1
  obtain ⟨ε, hε, hball⟩ := curve_ball D hg b hXL
  obtain ⟨K, hKc, hKO, hcvK⟩ : ∃ K : Set (Mat k r), IsCompact K ∧ K ⊆ Om k r D.z D.z' ∧
      ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ K :=
    ⟨(fun t : ℝ => cv b X t g) '' Metric.closedBall (0 : ℝ) ε,
      (isCompact_closedBall (0 : ℝ) ε).image (cv_continuous b X g),
      by rintro _ ⟨t, ht, rfl⟩; exact hball t ht,
      fun t ht => ⟨t, ht, rfl⟩⟩
  have hgK : g ∈ K := by
    have h0 := hcvK 0 (Metric.mem_closedBall_self hε.le)
    rwa [cv_zero] at h0
  have hKG : K ⊆ GV k r := fun x hx => (hKO hx).1
  obtain ⟨bb, hbbi, hbb⟩ := hDom2 K hKc hKO
  have hWSc : ({(u, v), (u2, v2)} : Set (List (Mat k r) × List (Mat k r))).Countable :=
    (Set.countable_singleton _).insert _
  have hWSl : ∀ uv ∈ ({(u, v), (u2, v2)} : Set (List (Mat k r) × List (Mat k r))),
      (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m := by
    intro uv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huv
    rcases huv with rfl | rfl
    · exact ⟨hu, hv, show u.length + v.length ≤ m by omega⟩
    · exact ⟨hu2, hv2, hl2⟩
  have hgood := good_set D hFm hKc hKG hWSc hWSl bb (fun uv huv x hx =>
    hbb uv.1 uv.2 (hWSl uv huv).1 (hWSl uv huv).2.1 (hWSl uv huv).2.2 x hx)
  obtain ⟨S, hSae, hSprop⟩ : ∃ S : Set (SS k r), (∀ᵐ p ∂D.μSS, p ∈ S) ∧ ∀ p ∈ S, D.inSS p ∧
      ∀ uv ∈ ({(u, v), (u2, v2)} : Set (List (Mat k r) × List (Mat k r))), ∀ x ∈ K,
        ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ bb p :=
    ⟨_, hgood, fun p hp => hp⟩
  obtain ⟨G, hGin, hGout⟩ : ∃ G : SS k r → Mat k r → (Wq →L[ℂ] Wp),
      (∀ p ∈ S, G p = dLR u v (rho D p F)) ∧ (∀ p ∉ S, G p = 0) :=
    ⟨fun p => S.indicator (fun p => dLR u v (rho D p F)) p,
      fun p hp => by dsimp only; exact Set.indicator_of_mem hp _,
      fun p hp => by dsimp only; simp [hp]⟩
  have hop0 : op b X (0 : Mat k r → (Wq →L[ℂ] Wp)) = 0 := by
    have h := hdl (fun _ => 0)
    rw [dLR_zero, dLR_zero] at h
    exact h.symm
  have hG1 : ∀ p, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G p) := by
    intro p
    by_cases hp : p ∈ S
    · rw [hGin p hp]
      exact ckOn_dLR_rho D (hSprop p hp).1 hFm hu hv 1 (by omega)
    · rw [hGout p hp]
      exact ckOn_zero _
  have hGm : ∀ t ∈ Metric.ball (0 : ℝ) ε, AEStronglyMeasurable (fun p => G p (cv b X t g)) D.μSS := by
    intro t ht
    refine (hDom1 u v hu hv (by omega) _ (hball t (Metric.ball_subset_closedBall ht))).congr ?_
    filter_upwards [hSae] with p hp
    rw [hGin p hp, dLR_rho D (hSprop p hp).1]
  have hG'm : AEStronglyMeasurable (fun p => op b X (G p) g) D.μSS := by
    refine (hDom1 u2 v2 hu2 hv2 hl2 g hg).congr ?_
    filter_upwards [hSae] with p hp
    rw [hGin p hp, ← hdl, dLR_rho D (hSprop p hp).1]
  have hb0 : ∀ p, ‖G p g‖ ≤ ‖bb p‖ := by
    intro p
    by_cases hp : p ∈ S
    · rw [hGin p hp]
      exact ((hSprop p hp).2 (u, v) (by simp) g hgK).trans (Real.le_norm_self _)
    · rw [hGout p hp]
      simp
  have hb1 : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ p, ‖op b X (G p) (cv b X t g)‖ ≤ ‖bb p‖ := by
    intro t ht p
    by_cases hp : p ∈ S
    · rw [hGin p hp, ← hdl]
      exact ((hSprop p hp).2 (u2, v2) (by simp) _
        (hcvK t (Metric.ball_subset_closedBall ht))).trans (Real.le_norm_self _)
    · rw [hGout p hp, hop0]
      simp
  have hΦ : ∀ t ∈ Metric.ball (0 : ℝ) ε,
      dLR u v (JF D F) (cv b X t g) = ∫ p, xiP D p • G p (cv b X t g) ∂D.μSS := by
    intro t ht
    rw [IH _ (hball t (Metric.ball_subset_closedBall ht))]
    refine integral_congr_ae ?_
    filter_upwards [hSae] with p hp
    rw [hGin p hp]
  have key := step_loc hXL (xiP D) (norm_xiP D) (continuous_xiP D).aestronglyMeasurable G hG1 hgG hε
    hGm hG'm (fun p => ‖bb p‖) hbbi.norm hb0 hb1 (dLR u v (JF D F)) hΦ
  rw [hdl, key]
  refine integral_congr_ae ?_
  filter_upwards [hSae] with p hp
  rw [hGin p hp, hdl]
end Formalism.FourierDecayAlt.P.LetterPairRecursion
