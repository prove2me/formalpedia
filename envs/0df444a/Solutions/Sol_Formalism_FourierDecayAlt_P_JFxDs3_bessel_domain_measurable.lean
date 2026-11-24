-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs3.bessel_domain_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:36.174799+00:00
-- url     : https://prove2.me/submissions/f9555ed6-fcd7-4529-970d-771c6a6bfb9a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_tele
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_lr_ad
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxDs3_unit_lr__0fb147390fef
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_adM_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_adM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_cont_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_le_sum_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cc_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_lrt_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Sd_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_conjugated_pair_continuous_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_of_contDiffOn_group
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_measurableSet_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_sgs_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JFxDs3
theorem _root_.solution : JFxDs2.JDomMeas := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hF u v hu hv hl g hg
  obtain ⟨c, hc⟩ := hF
  have hc0 : 0 ≤ c := cc_nonneg hc
  have hgG : g ∈ GV k r := hg.1
  have hA : 0 ≤ A := by
    have h1 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have h2 := lt_of_le_of_lt h1 hThr
    have h3 : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [lt_div_iff₀ h3, zero_mul] at h2
    have : (0 : ℝ) ≤ 6 * (r : ℝ) * (m : ℝ) := by positivity
    linarith
  have hwu : ∀ x ∈ lr u v, unitLie k r x.2 := unit_lr' hu hv
  have hwt : LRt ((lr u v).map Prod.fst) := lrt_lr u v
  have hwl : (lr u v).length ≤ m := by rw [length_lr]; exact hl
  have hx : ContinuousOn (fun p => sgs p g) {p : SS k r | D.inSS p} := B6.conjugated_pair_continuous_on D g
  have hxG : ∀ p ∈ {p : SS k r | D.inSS p}, sgs p g ∈ GV k r := fun p hp => B7.sgs_mem D hp hgG
  have hmain : ContinuousOn (fun p => W ((lr u v).map (adM p)) F (sgs p g)) {p : SS k r | D.inSS p} := by
    intro p₀ hp₀
    have hAL : AllLie ((lr u v).map (adM p₀)) := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact adM_lie hp₀ (hwu y' hy').1
    have hck : CkOn ((0 : ℕ) : ℕ∞) (GV k r) (W ((lr u v).map (adM p₀)) F) :=
      smooth_on_of_word_derivatives ((lr u v).map (adM p₀)) hAL 0 (ckOn_mono (by simpa using hwl) hc.1)
    have hsec : ContinuousWithinAt (fun p => W ((lr u v).map (adM p₀)) F (sgs p g)) {p : SS k r | D.inSS p} p₀ :=
      ((B6.continuousOn_of_contDiffOn_group hck).comp hx hxG) p₀ hp₀
    let Kf : SS k r → ℝ := fun p => 1 + ((lr u v).map fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖).sum
    let εf : SS k r → ℝ := fun p => ((lr u v).map fun x => ‖(adM p x).2 - (adM p₀ x).2‖).sum
    have hKc : ContinuousOn Kf {p : SS k r | D.inSS p} :=
      continuousOn_const.add (cont_sum _ (fun x p => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (lr u v)
        (fun x _ => (adM_cont D x).norm.add continuousOn_const))
    have hεc : ContinuousOn εf {p : SS k r | D.inSS p} :=
      cont_sum _ (fun x p => ‖(adM p x).2 - (adM p₀ x).2‖) (lr u v)
        (fun x _ => ((adM_cont D x).sub continuousOn_const).norm)
    have hε0 : εf p₀ = 0 := by simp [εf]
    let Bf : SS k r → ℝ := fun p => ((lr u v).length : ℝ) * (Kf p ^ m * εf p * c)
    have hBc : ContinuousWithinAt Bf {p : SS k r | D.inSS p} p₀ :=
      continuousWithinAt_const.mul ((((hKc p₀ hp₀).pow m).mul (hεc p₀ hp₀)).mul continuousWithinAt_const)
    have hB0 : Bf p₀ = 0 := by simp [Bf, hε0]
    have hd : Tendsto (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
      have hBt : Tendsto Bf (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
        have := hBc.tendsto; rwa [hB0] at this
      refine squeeze_zero_norm' ?_ hBt
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hxp := hxG p hp
      have hK1 : 1 ≤ Kf p := le_add_of_nonneg_right (List.sum_nonneg (by
        intro y hy
        obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
        positivity))
      have hT := tele hc hc0 hK1 (adM p) (adM p₀) (lr u v) [] (by simp)
        (by
          intro x hx
          have hmK := le_sum_map (fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (fun _ => by positivity) (lr u v) hx
          have hmε := le_sum_map (fun x => ‖(adM p x).2 - (adM p₀ x).2‖) (fun _ => norm_nonneg _) (lr u v) hx
          refine ⟨rfl, rfl, adM_lie hp (hwu x hx).1, adM_lie hp₀ (hwu x hx).1, ?_, ?_, hmε⟩
          · have := norm_nonneg (adM p₀ x).2
            show ‖(adM p x).2‖ ≤ Kf p
            simp only [Kf]; linarith
          · have := norm_nonneg (adM p x).2
            show ‖(adM p₀ x).2‖ ≤ Kf p
            simp only [Kf]; linarith)
        (by simpa using hwt) (by simpa using hwl) _ hxp
      simp only [List.nil_append] at hT
      have h1 : 1 ≤ gN (sgs p g) ^ A := Real.one_le_rpow (BetaSesquilinearity.gN_ge_one hxp) hA
      calc ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖
          ≤ gN (sgs p g) ^ A * ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖ :=
            le_mul_of_one_le_left (norm_nonneg _) h1
        _ ≤ Bf p := hT
    have hdc : ContinuousWithinAt
        (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        {p : SS k r | D.inSS p} p₀ := by
      have e0 : (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)) p₀ = 0 :=
        sub_self _
      unfold ContinuousWithinAt
      rw [e0]
      exact hd
    refine (hdc.add hsec).congr (fun p _ => ?_) ?_
    · simp
    · simp
  have hΦ : ContinuousOn (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) {p : SS k r | D.inSS p} := by
    have e : (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) =
        fun p => B6.Sd D p (W ((lr u v).map (adM p)) F (sgs p g)) := by
      funext p
      rw [B6.rho_eq, dLR_eq, lr_ad]
    rw [e]
    exact (B6.Sd_continuousOn D).clm_apply hmain
  have := hΦ.aestronglyMeasurable (μ := D.μSS) (B6.measurableSet_inSS D)
  have hr : D.μSS.restrict {p | D.inSS p} = D.μSS := Measure.restrict_eq_self_of_ae_mem (B5.ae_inSS D)
  rwa [hr] at this
end Formalism.FourierDecayAlt.P.JFxDs3
