-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rect_logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:38:19.039582+00:00
-- url     : https://prove2.me/submissions/a4a30981-37f4-47e3-822f-f14e0ad45bde

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectA
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFactor
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exr_abs_le
import Theorems.Thm_Formalism_FX_rectangle_residue
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exr_logDeriv
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exr_ord
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exr_term
import Theorems.Thm_Formalism_ZF_zeroFactorization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0) (y : ℝ) (hy : 0 < y)
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁) (hy₀ : y₀ < 0) (hy₁ : 0 < y₁)
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (f ρ = 0 ∧ x₀ < ρ.re ∧ ρ.re < x₁ ∧ y₀ < ρ.im ∧ ρ.im < y₁))
    (hedge : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → f w = 0 →
      x₀ < w.re ∧ w.re < x₁ ∧ y₀ < w.im ∧ w.im < y₁) :
    Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (-(deriv f 1 / f 1) * y - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ) := by
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = |x₀ - 1| + |x₁ - 1| + |y₀| + |y₁| + 1 := ⟨_, rfl⟩
  have hR₁ : 0 < R₁ := by rw [hR₁def]; positivity
  obtain ⟨Zb, m, h, hZb, hm, hh, hh0, hfac⟩ :=
    Formalism.ZF.zeroFactorization f 1 (R₁ + 1) R₁ hR₁ (by linarith) hf.differentiableOn hf1
  have hrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w a1 a2 a3 a4
    rw [Metric.mem_ball, dist_eq_norm]
    have e1 := Complex.norm_le_abs_re_add_abs_im (w - 1)
    have e2 : |(w - 1).re| ≤ |x₀ - 1| + |x₁ - 1| := by
      rw [sub_re, one_re]; exact exr_abs_le (by linarith) (by linarith)
    have e3 : |(w - 1).im| ≤ |y₀| + |y₁| := by
      rw [sub_im, one_im, sub_zero]; exact exr_abs_le a3 a4
    linarith
  have hball : Metric.ball (1 : ℂ) R₁ ⊆ Metric.closedBall 1 R₁ := Metric.ball_subset_closedBall
  have hSsub : Metric.ball (1 : ℂ) (R₁ + 1) ⊆ Metric.closedBall 1 (R₁ + 1) := Metric.ball_subset_closedBall
  have hR1S : Metric.ball (1 : ℂ) R₁ ⊆ Metric.ball 1 (R₁ + 1) := Metric.ball_subset_ball (by linarith)
  have hhS : DifferentiableOn ℂ h (Metric.ball 1 (R₁ + 1)) := hh.mono hSsub
  have hfacS : ∀ z ∈ Metric.ball (1 : ℂ) (R₁ + 1), f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    fun z hz => hfac z (hSsub hz)
  have hZin : ∀ ρ ∈ Z, ρ ∈ Metric.ball (1 : ℂ) R₁ := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hrect ρ a1.le a2.le a3.le a4.le
  have hZsub : Z ⊆ Zb := by
    intro ρ hρ
    exact (hZb ρ).2 ⟨hball (hZin ρ hρ), ((hZ ρ).1 hρ).1⟩
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := fun ρ hρ =>
    exr_ord f h Zb m _ Metric.isOpen_ball hhS hfacS ρ (hZsub hρ) (hR1S (hZin ρ hρ))
      (hh0 ρ (hball (hZin ρ hρ)))
  have h1Z : (1 : ℂ) ∉ Z := fun h => hf1 ((hZ 1).1 h).1
  have hZne0 : ∀ ρ ∈ Z, ρ ≠ 0 := by
    intro ρ hρ h0; have := ((hZ ρ).1 hρ).2.1; rw [h0, zero_re] at this; linarith
  have hZne1 : ∀ ρ ∈ Z, ρ ≠ 1 := fun ρ hρ h1 => h1Z (h1 ▸ hρ)

  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = Metric.ball (1 : ℂ) R₁ \ (((Zb \ Z : Finset ℂ) : Set ℂ) ∪ {0}) :=
    ⟨_, rfl⟩
  have hU : IsOpen U := by
    rw [hUdef]
    exact Metric.isOpen_ball.sdiff ((Finset.finite_toSet _).union (Set.finite_singleton 0)).isClosed
  have hUrect : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → w ∈ U := by
    intro w a1 a2 a3 a4
    rw [hUdef]
    refine ⟨hrect w a1 a2 a3 a4, ?_⟩
    rintro (hw | hw)
    · rw [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.mem_coe] at hw
      have hfw : f w = 0 := ((hZb w).1 hw.1).2
      obtain ⟨b1, b2, b3, b4⟩ := hedge w a1 a2 a3 a4 hfw
      exact hw.2 ((hZ w).2 ⟨hfw, b1, b2, b3, b4⟩)
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, zero_re] at a1; linarith
  have hUball : ∀ w ∈ U, w ∈ Metric.ball (1 : ℂ) R₁ := by
    intro w hw; rw [hUdef] at hw; exact hw.1
  have hUne0 : ∀ w ∈ U, w ≠ 0 := by
    intro w hw h0; rw [hUdef] at hw; exact hw.2 (Or.inr h0)
  have hUZb : ∀ w ∈ U, w ∉ Z → w ∉ Zb := by
    intro w hw hwZ hwZb; rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff]; exact ⟨hwZb, hwZ⟩))
  have h1U : (1 : ℂ) ∈ U := hUrect 1 (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have hZU : ∀ ρ ∈ Z, ρ ∈ U := by
    intro ρ hρ
    obtain ⟨_, a1, a2, a3, a4⟩ := (hZ ρ).1 hρ
    exact hUrect ρ a1.le a2.le a3.le a4.le

  obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ, φ = fun w => (y : ℂ) ^ w / w := ⟨_, rfl⟩
  obtain ⟨Lf, hLdef⟩ : ∃ Lf : ℂ → ℂ,
      Lf = fun w => deriv h w / h w + ∑ ρ ∈ Zb \ Z, (m ρ : ℂ) / (w - ρ) := ⟨_, rfl⟩
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hφU : DifferentiableOn ℂ φ U := by
    intro w hw
    rw [hφdef]
    exact ((differentiableAt_id.const_cpow (Or.inl hy0)).div differentiableAt_id
      (hUne0 w hw)).differentiableWithinAt
  have hLU : DifferentiableOn ℂ Lf U := by
    intro w hw
    have hwb := hR1S (hUball w hw)
    have hN : Metric.ball (1 : ℂ) (R₁ + 1) ∈ nhds w := Metric.isOpen_ball.mem_nhds hwb
    have hd1 : DifferentiableAt ℂ (deriv h) w :=
      ((hhS.deriv Metric.isOpen_ball) w hwb).differentiableAt hN
    have hd2 : DifferentiableAt ℂ h w := (hhS w hwb).differentiableAt hN
    have hhw : h w ≠ 0 := hh0 w (hball (hUball w hw))
    rw [hLdef]
    refine (DifferentiableAt.add (hd1.div hd2 hhw) ?_).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun ρ hρ => ?_
    refine (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) ?_
    rw [Finset.mem_sdiff] at hρ
    intro h0; rw [sub_eq_zero] at h0
    rw [hUdef] at hw
    exact hw.2 (Or.inl (by rw [Finset.coe_sdiff, h0]; exact ⟨hρ.1, hρ.2⟩))
  have hLD : ∀ w ∈ U, w ∉ Z → deriv f w / f w = (∑ ρ ∈ Z, (m ρ : ℂ) / (w - ρ)) + Lf w := by
    intro w hw hwZ
    rw [exr_logDeriv f h Zb m _ Metric.isOpen_ball hhS hfacS w (hR1S (hUball w hw)) (hUZb w hw hwZ)
      (hh0 w (hball (hUball w hw))), hLdef, ← Finset.sum_sdiff hZsub]
    ring
  have hk : ∀ w, exKer y w = φ w / (w - 1) := fun w => by rw [hφdef, exKer, div_div]
  have hb1 : ∃ b : ℂ → ℂ, b 1 = -(deriv f 1 / f 1) * y ∧ ∀ ρ ∈ Z, b ρ = -(m ρ : ℂ) * exKer y ρ :=
    ⟨fun p => if p = 1 then -(deriv f 1 / f 1) * y else -(m p : ℂ) * exKer y p, by simp,
      fun ρ hρ => by simp [hZne1 ρ hρ]⟩
  obtain ⟨b, hb1, hbρ⟩ := hb1
  obtain ⟨G₀, hG₀def⟩ : ∃ G₀ : ℂ → ℂ, G₀ = fun w => -dslope (fun z => Lf z * φ z) 1 w -
      ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := ⟨_, rfl⟩
  have hG₀U : DifferentiableOn ℂ G₀ U := by
    rw [hG₀def]
    refine DifferentiableOn.sub ((differentiableOn_dslope (hU.mem_nhds h1U)).2 (hLU.mul hφU)).neg ?_
    refine DifferentiableOn.fun_sum fun ρ hρ => ?_
    exact (differentiableOn_const _).mul (((differentiableOn_dslope (hU.mem_nhds (hZU ρ hρ))).2 hφU).sub
      ((differentiableOn_dslope (hU.mem_nhds h1U)).2 hφU))
  have hφw : ∀ z, φ z = (y : ℂ) ^ z / z := fun z => by rw [hφdef]
  have hφ1 : φ 1 = y := by rw [hφw]; simp
  have hkey : ∀ w ∈ U, w ∉ insert 1 Z →
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) = G₀ w := by
    intro w hw hwP
    rw [Finset.mem_insert, not_or] at hwP
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 hwP.1
    have hw0 := hUne0 w hw
    have hwρ : ∀ ρ ∈ Z, w - ρ ≠ 0 := fun ρ hρ h0 => hwP.2 (sub_eq_zero.1 h0 ▸ hρ)
    have hC : ∑ ρ ∈ Z, b ρ / (w - ρ) = ∑ ρ ∈ Z, -(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1))) / (w - ρ) :=
      Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, exKer]
    have hD : ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) =
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1)) :=
      Finset.sum_congr rfl fun ρ hρ => by
        rw [dslope_of_ne _ (sub_ne_zero.1 (hwρ ρ hρ)), dslope_of_ne _ hwP.1, slope_def_field,
          slope_def_field, hφ1, hφw, hφw]
    have hrel : ∑ ρ ∈ Z, (-((m ρ : ℂ) / (w - ρ)) * ((y : ℂ) ^ w / w / (w - 1)) +
        (m ρ : ℂ) / (1 - ρ) * y / (w - 1) - (-(m ρ : ℂ) * ((y : ℂ) ^ ρ / (ρ * (ρ - 1)))) / (w - ρ) +
        (m ρ : ℂ) / (ρ - 1) * (((y : ℂ) ^ w / w - (y : ℂ) ^ ρ / ρ) / (w - ρ) -
          ((y : ℂ) ^ w / w - y) / (w - 1))) = 0 :=
      Finset.sum_eq_zero fun ρ hρ => exr_term _ _ _ _ _ _ hw0 hw1 (hwρ ρ hρ) (hZne0 ρ hρ)
        (sub_ne_zero.2 (hZne1 ρ hρ))
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hrel
    have hG₀w : G₀ w = -dslope (fun z => Lf z * φ z) 1 w -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (ρ - 1) * (dslope φ ρ w - dslope φ 1 w) := by rw [hG₀def]
    rw [hG₀w, hD, Finset.sum_insert h1Z, hC, hb1, dslope_of_ne _ hwP.1, slope_def_field, hLD w hw hwP.2,
      hLD 1 h1U h1Z, hk w, hφ1, hφw w]
    linear_combination hrel
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun w => if w ∈ insert 1 Z then G₀ w else
      -(deriv f w / f w) * exKer y w - ∑ p ∈ insert 1 Z, b p / (w - p) := ⟨_, rfl⟩
  have hGU : DifferentiableOn ℂ G U := by
    refine hG₀U.congr fun w hw => ?_
    rw [hGdef]
    by_cases hwP : w ∈ insert 1 Z
    · simp only [if_pos hwP]
    · simp only [if_neg hwP]; exact hkey w hw hwP
  have hPin : ∀ p ∈ insert 1 Z, x₀ < p.re ∧ p.re < x₁ ∧ y₀ < p.im ∧ p.im < y₁ := by
    intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with hp | hp
    · subst hp; simp; exact ⟨hx₀1, hx₁, hy₀, hy₁⟩
    · exact ((hZ p).1 hp).2
  have hsub : (Set.uIcc x₀ x₁ ×ℂ Set.uIcc y₀ y₁) ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hw
    exact hUrect w hw.1.1 hw.1.2 hw.2.1 hw.2.2
  have hres := Formalism.FX.rectangle_residue (fun w => -(deriv f w / f w) * exKer y w) G (insert 1 Z) b
    x₀ x₁ y₀ y₁ (by linarith) (by linarith) hPin ⟨U, hU, hsub, hGU⟩ (fun w hw => by
      rw [hGdef]; simp only [if_neg hw]; ring)
  have hsum : ∑ ρ ∈ Z, b ρ = -∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ρ hρ => by rw [hbρ ρ hρ, hord ρ hρ, neg_mul]
  rw [show Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
    Formalism.FX.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ from rfl, hres,
    Finset.sum_insert h1Z, hb1, hsum]
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
