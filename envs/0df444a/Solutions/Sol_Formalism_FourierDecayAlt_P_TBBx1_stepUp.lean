-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.stepUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:44.067596+00:00
-- url     : https://prove2.me/submissions/ee598dd8-b6e1-4047-ab67-f5bd2aa985c3

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_mn_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_min_le_truncated_exponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_truncated_exponential_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_fsv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_gauss_const
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gaussian_lattice_cutoff_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution : StepUp := by
  refine ⟨40.5 / π, by positivity, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hPos hI4 hI5 b s hb hs hbs h hh w hw hlen Mb hMb z hz
  have hΛ0 : 0 < Λ := by linarith
  have hMb0 : 0 ≤ Mb :=
    (hPos _ w _ hw (by omega)).trans (hMb w (isExt_self hw (by omega)) 1 one_ne_zero)
  set ω₁ : ℂ := ((π / Λ : ℝ) : ℂ) with hω₁
  set ω₂ : ℂ := ((π / Λ : ℝ) : ℂ) * Complex.I with hω₂
  have him : (conj ω₁ * ω₂).im = (π / Λ) ^ 2 := by
    simp [hω₁, hω₂, Complex.conj_ofReal]
    ring
  have hne : (conj ω₁ * ω₂).im ≠ 0 := by rw [him]; positivity
  have hbdd : ∀ w', IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)])) :=
    fun w' hw' => ⟨Mb, by rintro _ ⟨t, rfl⟩; exact hMb w' hw' t.1 t.2⟩
  obtain ⟨k, hk1, hk2⟩ := hI5 b s hb hs hbs h hh w hw hlen hbdd ω₁ ω₂ z hne
  have hkσ : ∀ σ, InDual ω₁ ω₂ σ → (‖k σ‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (mn Λ K ‖σ‖ * Mb) := by
    intro σ hσ
    refine (hk2 σ hσ).trans (limsup_le_of_le (by isBoundedDefault) ?_)
    have ev1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
    have ev2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t⁻¹ + σ ≠ 0 := by
      by_cases hσ0 : σ = 0
      · filter_upwards [ev1] with t ht
        simpa [hσ0] using ht
      · have hn : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ (-σ)⁻¹ :=
          eventually_ne_nhds (by simpa using hσ0)
        filter_upwards [nhdsWithin_le_nhds hn] with t ht
        intro h0
        apply ht
        rw [← eq_neg_iff_add_eq_zero.2 h0, inv_inv]
    filter_upwards [ev1, ev2] with t ht ht'
    have ht'' : (t⁻¹ + σ)⁻¹ ≠ 0 := inv_ne_zero ht'
    obtain ⟨w₁, w₂, hw₁, hw₂, hN⟩ := hI4 b (s - 1) hb (by omega) (by omega) h hh w hw hlen t _ ht ht''
    rw [show b + (s - 1) - 1 = b + s - 2 by omega] at hN
    have hdiff : ‖t⁻¹ - ((t⁻¹ + σ)⁻¹)⁻¹‖ = ‖σ‖ := by
      rw [inv_inv, sub_add_cancel_left, norm_neg]
    rw [hdiff] at hN
    have hE1 := hMb w₁ hw₁ t ht
    have hE2 := hMb w₂ hw₂ _ ht''
    have hmn := mn_nonneg hΛ0.le K (norm_nonneg σ)
    have hle : ‖NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, (t⁻¹ + σ)⁻¹)])‖ ≤
        mn Λ K ‖σ‖ * Mb := hN.trans (mul_le_mul_of_nonneg_left (by linarith) hmn)
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hle
  have hdual : ∀ σ, InDual ω₁ ω₂ σ → σ ∈ Set.range (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a) := by
    intro σ hσ
    have h1 := hσ 1 0
    have h2 := hσ 0 1
    simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at h1 h2
    rw [fsv_eq, Complex.exp_eq_one_iff] at h1 h2
    obtain ⟨n1, hn1⟩ := h1
    obtain ⟨n2, hn2⟩ := h2
    have e1 := congrArg Complex.im hn1
    have e2 := congrArg Complex.im hn2
    simp [hω₁, hω₂, Complex.mul_im, Complex.mul_re] at e1 e2
    refine ⟨⟨n2, n1⟩, ?_⟩
    show (Λ : ℂ) * GaussianInt.toComplex ⟨n2, n1⟩ = σ
    rw [GaussianInt.toComplex_def']
    have hπ := Real.pi_pos
    apply Complex.ext
    · simp
      field_simp at e2
      nlinarith
    · simp
      field_simp at e1
      nlinarith
  have hinj : Function.Injective (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a) := by
    intro a a' haa
    have : GaussianInt.toComplex a = GaussianInt.toComplex a' :=
      mul_left_cancel₀ (by exact_mod_cast hΛ0.ne') haa
    exact GaussianInt.toComplex_injective this
  let g : ℂ → ℝ≥0∞ := fun σ => ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 Λ ‖σ‖)
  have hG : ∑' a : GaussianInt, g ((Λ : ℂ) * GaussianInt.toComplex a) ≤ ENNReal.ofReal 40.5 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun S => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => truncated_exponential_nonneg _ _ hΛ0.le (norm_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Formalism.HermitianLatticeCounting.P.gaussian_lattice_cutoff_sum 3 Λ (by norm_num) hΛ0 S
    rwa [gauss_const] at this
  have hsum : ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, (‖k σ.1‖₊ : ℝ≥0∞) ≤
      ENNReal.ofReal Mb * ENNReal.ofReal 40.5 := by
    calc ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, (‖k σ.1‖₊ : ℝ≥0∞)
        ≤ ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, ENNReal.ofReal Mb * g σ.1 := by
          refine ENNReal.tsum_le_tsum fun σ => (hkσ σ.1 σ.2).trans ?_
          rw [← ENNReal.ofReal_mul hMb0, mul_comm Mb]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hMb0)
          exact min_le_truncated_exponential hΛ0.le le_rfl hK (norm_nonneg _)
      _ = ENNReal.ofReal Mb * ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, g σ.1 := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal Mb *
            ∑' σ : Set.range (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a), g σ.1 := by
          gcongr
          exact ENNReal.tsum_mono_subtype g (fun σ hσ => hdual σ hσ)
      _ = ENNReal.ofReal Mb * ∑' a : GaussianInt, g ((Λ : ℂ) * GaussianInt.toComplex a) := by
          rw [tsum_range g hinj]
      _ ≤ ENNReal.ofReal Mb * ENNReal.ofReal 40.5 := by gcongr
  have hterm : ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤
      ∑' ab : ℤ × ℤ, ENNReal.ofReal
        (Ew p nn F (b + s - 1) w (h ++ [(s, z + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)])) := by
    refine le_of_eq_of_le ?_ (ENNReal.le_tsum ((0 : ℤ), (0 : ℤ)))
    simp
  have hv : |(conj ω₁ * ω₂).im| / π = π / Λ ^ 2 := by
    rw [him, abs_of_nonneg (by positivity)]
    field_simp
  have hmain : ENNReal.ofReal (π / Λ ^ 2 * Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤
      ENNReal.ofReal (Mb * 40.5) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hMb0, ← hv]
    have hm : ENNReal.ofReal (|(conj ω₁ * ω₂).im| / π) * ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤
        ENNReal.ofReal (|(conj ω₁ * ω₂).im| / π) * ∑' ab : ℤ × ℤ, ENNReal.ofReal
          (Ew p nn F (b + s - 1) w (h ++ [(s, z + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)])) := by gcongr
    exact hm.trans (hk1.trans hsum)
  have hfin := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain
  have hπ := Real.pi_pos
  have hΛ2 : 0 < Λ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hΛ2] at hfin
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hπ]
  nlinarith
end Formalism.FourierDecayAlt.P.TBBx1
