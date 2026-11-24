-- Prove2me | solution 1 for FaulhuberTFA.stft_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:33:12.454031+00:00
-- url     : https://prove2.me/submissions/4c8b10b8-f372-47d2-bf91-bfbc8fbda599

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

set_option autoImplicit false

/-!
Moyal's formula (orthogonality relations of the STFT), proved without density arguments:
* Plancherel for `L¹ ∩ L²` functions (`mo_fourier_toLp_ae_eq`, via tempered distributions);
* for a.e. `x`, the window product `t ↦ f t * conj (g (t - x))` lies in `L¹ ∩ L²`, and
  `stft g f x = 𝓕 (t ↦ f t * conj (g (t - x)))`;
* Tonelli / Fubini on `Rd d × Rd d` and translation invariance.
-/

namespace FaulhuberTFA

open scoped FourierTransform SchwartzMap ENNReal

section General
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem mo_eLpNorm_two_sq (u : α → ℂ) : eLpNorm u 2 μ ^ 2 = ∫⁻ t, ‖u t‖ₑ ^ 2 ∂μ := by
  have a := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := u) (p := 2) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at a
  norm_cast at a

theorem mo_eLpNorm_two_eq (u : α → ℂ) :
    eLpNorm u 2 μ = (∫⁻ t, ‖u t‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [← mo_eLpNorm_two_sq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem mo_lintegral_sq_lt_top {u : α → ℂ} (hu : MemLp u 2 μ) : ∫⁻ t, ‖u t‖ₑ ^ 2 ∂μ < ∞ := by
  rw [← mo_eLpNorm_two_sq]
  exact ENNReal.pow_lt_top hu.2

theorem mo_memLp_two_of_lintegral {u : α → ℂ} (hm : AEStronglyMeasurable u μ)
    (hu : ∫⁻ t, ‖u t‖ₑ ^ 2 ∂μ < ∞) : MemLp u 2 μ := by
  refine ⟨hm, ?_⟩
  rw [mo_eLpNorm_two_eq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hu.ne

end General

section Plancherel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section
open scoped ContDiff

/-- For `h ∈ L¹ ∩ L²`, the `L²` Fourier transform agrees a.e. with the Fourier integral. -/
theorem mo_fourier_toLp_ae_eq {h : V → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕 h := by
  apply _root_.ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner h1).locallyIntegrable
  intro φ hφ hcs
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hcs.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := Complex.ofRealCLM.contDiff.comp hφ
  set ψ := hg₁.toSchwartzMap hg₂ with hψ
  have hψφ : ∀ x, ψ x = (φ x : ℂ) := fun x => rfl
  set H : Lp ℂ 2 (volume : Measure V) := h2.toLp h
  have key : ∫ x, ψ x • (𝓕 H : Lp ℂ 2 (volume : Measure V)) x = ∫ x, (𝓕 ψ) x • H x := by
    have := congrArg (fun T : 𝓢'(V, ℂ) => T ψ) (Lp.fourier_toTemperedDistribution_eq H)
    simpa using this.symm
  have e1 : ∫ x, (𝓕 ψ) x • H x = ∫ x, (𝓕 ψ) x • h x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  have e2 : ∫ x, (𝓕 ψ) x • h x = ∫ x, ψ x • 𝓕 h x := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner ψ.integrable h1)
  simp only [← Complex.coe_smul, ← hψφ]
  rw [key, e1, e2]

end

theorem mo_memLp_fourier {h : V → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    MemLp (𝓕 h) 2 :=
  (Lp.memLp _).ae_eq (mo_fourier_toLp_ae_eq h1 h2)

theorem mo_eLpNorm_fourier {h : V → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    eLpNorm (𝓕 h) 2 volume = eLpNorm h 2 volume := by
  have e1 := eLpNorm_congr_ae (p := 2) (mo_fourier_toLp_ae_eq h1 h2)
  have e2 := eLpNorm_congr_ae (p := 2) h2.coeFn_toLp
  have := Lp.norm_fourier_eq (h2.toLp h)
  rw [Lp.norm_def, Lp.norm_def, ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _)
    (Lp.eLpNorm_ne_top _)] at this
  rw [← e1, this, e2]

theorem mo_lintegral_fourier_sq {h : V → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    ∫⁻ ξ, ‖𝓕 h ξ‖ₑ ^ 2 = ∫⁻ t, ‖h t‖ₑ ^ 2 := by
  have := mo_eLpNorm_fourier h1 h2
  have k := fun (u : V → ℂ) => eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := u) (p := 2) (by norm_num)
  have a := k (𝓕 h)
  have b := k h
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at a b
  norm_cast at a b
  rw [← a, ← b, this]

theorem mo_integral_fourier_mul_conj {h₁ h₂ : V → ℂ} (h₁1 : Integrable h₁) (h₁2 : MemLp h₁ 2)
    (h₂1 : Integrable h₂) (h₂2 : MemLp h₂ 2) :
    ∫ ξ, 𝓕 h₁ ξ * starRingEnd ℂ (𝓕 h₂ ξ) = ∫ t, h₁ t * starRingEnd ℂ (h₂ t) := by
  have := Lp.inner_fourier_eq (h₂2.toLp h₂) (h₁2.toLp h₁)
  rw [L2.inner_def, L2.inner_def] at this
  simp only [RCLike.inner_apply] at this
  have e1 : ∫ ξ, 𝓕 h₁ ξ * starRingEnd ℂ (𝓕 h₂ ξ) =
      ∫ a, (𝓕 (h₁2.toLp h₁) : Lp ℂ 2 (volume : Measure V)) a *
        starRingEnd ℂ ((𝓕 (h₂2.toLp h₂) : Lp ℂ 2 (volume : Measure V)) a) := by
    apply integral_congr_ae
    filter_upwards [mo_fourier_toLp_ae_eq h₁1 h₁2, mo_fourier_toLp_ae_eq h₂1 h₂2] with a ha hb
    rw [ha, hb]
  have e2 : ∫ t, h₁ t * starRingEnd ℂ (h₂ t) =
      ∫ a, (h₁2.toLp h₁ : Lp ℂ 2 (volume : Measure V)) a *
        starRingEnd ℂ ((h₂2.toLp h₂ : Lp ℂ 2 (volume : Measure V)) a) := by
    apply integral_congr_ae
    filter_upwards [h₁2.coeFn_toLp, h₂2.coeFn_toLp] with a ha hb
    rw [ha, hb]
  rw [e1, e2, this]

end Plancherel

section STFT

variable {d : ℕ}

theorem mo_stft_eq_fourier (g f : Rd d → ℂ) (x ω : Rd d) :
    stft g f x ω = 𝓕 (fun t => f t * starRingEnd ℂ (g (t - x))) ω := by
  rw [Real.fourier_eq']
  unfold stft ePhase
  congr 1; funext t
  rw [smul_eq_mul, real_inner_comm]
  push_cast
  ring_nf

/-- The map `(x, t) ↦ t - x` is quasi-measure-preserving. -/
theorem mo_qmp_sub_swap :
    Measure.QuasiMeasurePreserving (fun p : Rd d × Rd d => p.2 - p.1)
      ((volume : Measure (Rd d)).prod volume) volume :=
  (quasiMeasurePreserving_sub volume volume).comp
    Measure.measurePreserving_swap.quasiMeasurePreserving

theorem mo_aesm_win {f g : Rd d → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun p : Rd d × Rd d => f p.2 * starRingEnd ℂ (g (p.2 - p.1)))
      ((volume : Measure (Rd d)).prod volume) := by
  have h1 : AEStronglyMeasurable (fun p : Rd d × Rd d => f p.2)
      ((volume : Measure (Rd d)).prod volume) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have h2 := hg.comp_quasiMeasurePreserving (mo_qmp_sub_swap (d := d))
  exact h1.mul (Complex.continuous_conj.comp_aestronglyMeasurable h2)

theorem mo_memLp_conj_transl {g : Rd d → ℂ} (hg : MemLp g 2 volume) (x : Rd d) :
    MemLp (fun t => starRingEnd ℂ (g (t - x))) 2 volume :=
  (hg.comp_measurePreserving (measurePreserving_sub_right volume x)).star

theorem mo_integrable_win {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x : Rd d) : Integrable (fun t => f t * starRingEnd ℂ (g (t - x))) volume :=
  hf.integrable_mul (mo_memLp_conj_transl hg x)

theorem mo_lintegral_conv (a b : Rd d → ℝ≥0∞) (ha : AEMeasurable a volume)
    (hb : AEMeasurable b volume) :
    ∫⁻ p : Rd d × Rd d, a p.2 * b (p.2 - p.1) ∂((volume : Measure (Rd d)).prod volume) =
      (∫⁻ t, a t) * ∫⁻ t, b t := by
  have hm : AEMeasurable (fun p : Rd d × Rd d => a p.2 * b (p.2 - p.1))
      ((volume : Measure (Rd d)).prod volume) :=
    (ha.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      (hb.comp_quasiMeasurePreserving mo_qmp_sub_swap)
  rw [lintegral_prod_symm _ hm]
  calc ∫⁻ t, ∫⁻ x, a t * b (t - x) = ∫⁻ t, a t * ∫⁻ x, b x := by
        congr 1; funext t
        rw [lintegral_const_mul'' (a t) (f := fun x => b (t - x)) (hb.comp_quasiMeasurePreserving
          (Measure.measurePreserving_sub_left volume t).quasiMeasurePreserving),
          lintegral_sub_left_eq_self b t]
    _ = _ := lintegral_mul_const'' _ ha

theorem mo_integrable_conv {a b : Rd d → ℂ} (ha : Integrable a volume) (hb : Integrable b volume) :
    Integrable (fun p : Rd d × Rd d => a p.2 * b (p.2 - p.1))
      ((volume : Measure (Rd d)).prod volume) := by
  refine ⟨(ha.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      (hb.1.comp_quasiMeasurePreserving mo_qmp_sub_swap), ?_⟩
  unfold HasFiniteIntegral
  simp_rw [enorm_mul]
  rw [mo_lintegral_conv _ _ ha.1.enorm hb.1.enorm]
  exact ENNReal.mul_lt_top ha.2 hb.2

theorem mo_lintegral_win_sq {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫⁻ p : Rd d × Rd d, ‖f p.2 * starRingEnd ℂ (g (p.2 - p.1))‖ₑ ^ 2
      ∂((volume : Measure (Rd d)).prod volume) = (∫⁻ t, ‖f t‖ₑ ^ 2) * ∫⁻ t, ‖g t‖ₑ ^ 2 := by
  simp_rw [enorm_mul, RCLike.enorm_conj, mul_pow]
  exact mo_lintegral_conv _ _ (hf.1.enorm.pow_const 2) (hg.1.enorm.pow_const 2)

theorem mo_ae_memLp_win {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∀ᵐ x ∂(volume : Measure (Rd d)), MemLp (fun t => f t * starRingEnd ℂ (g (t - x))) 2 volume := by
  have hm := (mo_aesm_win hf.1 hg.1).enorm.pow_const 2
  have hlt := mo_lintegral_win_sq hf hg
  rw [lintegral_prod _ hm] at hlt
  have hfin : ∫⁻ x, ∫⁻ t, ‖f t * starRingEnd ℂ (g (t - x))‖ₑ ^ 2 < ∞ := by
    rw [hlt]; exact ENNReal.mul_lt_top (mo_lintegral_sq_lt_top hf) (mo_lintegral_sq_lt_top hg)
  filter_upwards [ae_lt_top' hm.lintegral_prod_right' hfin.ne] with x hx
  exact mo_memLp_two_of_lintegral (mo_integrable_win hf hg x).1 hx

theorem mo_stft_aestronglyMeasurable {f g : Rd d → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun p : Rd d × Rd d => stft g f p.1 p.2) volume := by
  rw [Measure.volume_eq_prod]
  have hq : Measure.QuasiMeasurePreserving (fun q : (Rd d × Rd d) × Rd d => (q.1.1, q.2))
      (((volume : Measure (Rd d)).prod volume).prod volume) ((volume : Measure (Rd d)).prod volume) :=
    QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_fst (Measure.QuasiMeasurePreserving.id volume)
  have hK : AEStronglyMeasurable (fun q : (Rd d × Rd d) × Rd d =>
      f q.2 * starRingEnd ℂ (g (q.2 - q.1.1)) * ePhase (-⟪q.1.2, q.2⟫_ℝ))
      (((volume : Measure (Rd d)).prod volume).prod volume) :=
    ((mo_aesm_win hf hg).comp_quasiMeasurePreserving hq).mul
      (Continuous.aestronglyMeasurable (by unfold ePhase; fun_prop))
  exact hK.integral_prod_right'

/-- Energy identity: `∫∫ |V_g f|² = ‖f‖₂² ‖g‖₂²` (in `ℝ≥0∞`). -/
theorem mo_lintegral_stft_sq {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫⁻ p : Rd d × Rd d, ‖stft g f p.1 p.2‖ₑ ^ 2 = (∫⁻ t, ‖f t‖ₑ ^ 2) * ∫⁻ t, ‖g t‖ₑ ^ 2 := by
  have hm := (mo_stft_aestronglyMeasurable hf.1 hg.1).enorm.pow_const 2
  rw [Measure.volume_eq_prod] at hm ⊢
  rw [← mo_lintegral_win_sq hf hg, lintegral_prod _ hm,
    lintegral_prod _ ((mo_aesm_win hf.1 hg.1).enorm.pow_const 2)]
  apply lintegral_congr_ae
  filter_upwards [mo_ae_memLp_win hf hg] with x hx
  simp only [mo_stft_eq_fourier]
  exact mo_lintegral_fourier_sq (mo_integrable_win hf hg x) hx

theorem mo_stft_memLp {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    MemLp (fun p : Rd d × Rd d => stft g f p.1 p.2) 2 volume := by
  refine mo_memLp_two_of_lintegral (mo_stft_aestronglyMeasurable hf.1 hg.1) ?_
  rw [mo_lintegral_stft_sq hf hg]
  exact ENNReal.mul_lt_top (mo_lintegral_sq_lt_top hf) (mo_lintegral_sq_lt_top hg)

theorem mo_eLpNorm_stft {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    eLpNorm (fun p : Rd d × Rd d => stft g f p.1 p.2) 2 volume =
      eLpNorm f 2 volume * eLpNorm g 2 volume := by
  rw [mo_eLpNorm_two_eq, mo_eLpNorm_two_eq f, mo_eLpNorm_two_eq g, mo_lintegral_stft_sq hf hg,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

/-- Moyal's formula (orthogonality relations of the STFT). -/
theorem mo_integral_stft_mul_conj {f₁ f₂ g₁ g₂ : Rd d → ℂ}
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg₁ : MemLp g₁ 2 volume)
    (hg₂ : MemLp g₂ 2 volume) :
    ∫ p : Rd d × Rd d, stft g₁ f₁ p.1 p.2 * starRingEnd ℂ (stft g₂ f₂ p.1 p.2) =
      l2inner f₁ f₂ * starRingEnd ℂ (l2inner g₁ g₂) := by
  set a : Rd d → ℂ := fun t => f₁ t * starRingEnd ℂ (f₂ t) with ha_def
  set b : Rd d → ℂ := fun s => starRingEnd ℂ (g₁ s) * g₂ s with hb_def
  have ha : Integrable a volume := hf₁.integrable_mul hf₂.star
  have hb : Integrable b volume := hg₁.star.integrable_mul hg₂
  have hint : Integrable (fun p : Rd d × Rd d =>
      stft g₁ f₁ p.1 p.2 * starRingEnd ℂ (stft g₂ f₂ p.1 p.2)) volume :=
    (mo_stft_memLp hf₁ hg₁).integrable_mul (mo_stft_memLp hf₂ hg₂).star
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  have step : (fun x => ∫ ω, stft g₁ f₁ x ω * starRingEnd ℂ (stft g₂ f₂ x ω)) =ᵐ[volume]
      (fun x => ∫ t, a t * b (t - x)) := by
    filter_upwards [mo_ae_memLp_win hf₁ hg₁, mo_ae_memLp_win hf₂ hg₂] with x h1 h2
    simp only [mo_stft_eq_fourier]
    rw [mo_integral_fourier_mul_conj (mo_integrable_win hf₁ hg₁ x) h1
      (mo_integrable_win hf₂ hg₂ x) h2]
    congr 1; funext t
    simp only [ha_def, hb_def, map_mul, Complex.conj_conj]
    ring
  rw [integral_congr_ae step]
  have hab := mo_integrable_conv ha hb
  rw [← integral_prod (fun p : Rd d × Rd d => a p.2 * b (p.2 - p.1)) hab,
    integral_prod_symm _ hab]
  simp_rw [integral_const_mul, integral_sub_left_eq_self]
  rw [integral_mul_const]
  unfold l2inner
  congr 1
  rw [← integral_conj]
  congr 1; funext s
  simp [hb_def, map_mul]

end STFT

end FaulhuberTFA

open FaulhuberTFA in
theorem solution {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    eLpNorm (fun p : Rd d × Rd d => stft g f p.1 p.2) 2 volume = eLpNorm f 2 volume * eLpNorm g 2 volume ∧
    (eLpNorm g 2 volume = 1 → eLpNorm f 2 volume = eLpNorm (fun p : Rd d × Rd d => stft g f p.1 p.2) 2 volume) := by
  refine ⟨mo_eLpNorm_stft hf hg, fun h1 => ?_⟩
  rw [mo_eLpNorm_stft hf hg, h1, mul_one]
