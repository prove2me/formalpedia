-- Prove2me | solution 1 for DimdPolyLEAN.equalAmbiguity_to_rankOneKernel_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:42.419437+00:00
-- url     : https://prove2.me/submissions/c0db6766-3ed0-40af-bac8-807af01086c8

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private lemma integral_fourier_schwartz_mul_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {h : V -> ℂ} (hh1 : Integrable h) (phi : 𝓢(V, ℂ)) :
    ∫ x : V, ((𝓕 phi) x) * h x =
      ∫ ξ : V, phi ξ * ((𝓕 h) ξ) := by
  have hswap := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (M := ContinuousLinearMap.mul ℂ ℂ)
      (e := Real.fourierChar)
      (μ := (volume : Measure V))
      (ν := (volume : Measure V))
      (L := innerₗ V)
      Real.continuous_fourierChar
      continuous_inner
      hh1
      phi.integrable
  calc
    ∫ x : V, ((𝓕 phi) x) * h x =
        ∫ x : V, h x * ((𝓕 (phi : V -> ℂ)) x) := by simp [SchwartzMap.fourier_coe, mul_comm]
    _ = ∫ ξ : V, ((𝓕 h) ξ) * phi ξ := by
          have hflip :
              (fun x : V => h x * (𝓕 (⇑phi)) x) =
                fun x : V => ((ContinuousLinearMap.mul ℂ ℂ) (h x))
                  (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V).flip
                    (⇑phi) x) := by
            funext x
            rw [ContinuousLinearMap.mul_apply', Real.fourier_eq]
            simp only [VectorFourier.fourierIntegral]
            simp_all only [ContinuousLinearMap.mul_apply', flip_innerₗ, innerₗ_apply_apply]
          rw [hflip]
          simpa [ContinuousLinearMap.mul_apply', Real.fourier_eq,
            VectorFourier.fourierIntegral] using hswap.symm
    _ = ∫ ξ : V, phi ξ * ((𝓕 h) ξ) := by simp [mul_comm]
private theorem fourier_l1_l2_eq_zero_ae
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {h : V -> ℂ}
    (hh1 : Integrable h) (hh2 : MemLp h 2 (volume : Measure V))
    (hFourier : ∀ ξ : V, (𝓕 h) ξ = 0) :
    h =ᵐ[(volume : Measure V)] fun _ => (0 : ℂ) := by
  let H : Lp ℂ 2 (volume : Measure V) := hh2.toLp h
  have hH_coe :
      ((H : Lp ℂ 2 (volume : Measure V)) : V -> ℂ)
        =ᵐ[(volume : Measure V)] h := by exact hh2.coeFn_toLp
  have hdist_fourier_zero :
      ((𝓕 H : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) = 0 := by
    calc
      ((𝓕 H : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
          𝓕 (H : 𝓢'(V, ℂ)) := by rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      _ = 0 := by
            ext phi
            calc
              (𝓕 (H : 𝓢'(V, ℂ))) phi =
                  (H : 𝓢'(V, ℂ)) (𝓕 phi) := by simp
              _ = ∫ x : V, ((𝓕 phi) x) * h x := by
                    rw [MeasureTheory.Lp.toTemperedDistribution_apply]
                    apply integral_congr_ae
                    filter_upwards [hH_coe] with x hx
                    simp [hx, smul_eq_mul]
              _ = ∫ ξ : V, phi ξ * ((𝓕 h) ξ) :=
                    integral_fourier_schwartz_mul_eq hh1 phi
              _ = 0 := by simp [hFourier]
  have hFH_zero : 𝓕 H = 0 := by
    have hker :
        𝓕 H ∈
          (MeasureTheory.Lp.toTemperedDistributionCLM
            ℂ (volume : Measure V) 2).ker := by
      simp_all only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        Lp.toTemperedDistributionCLM_apply]
    have hker_bot :=
      MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
        (F := ℂ) (μ := (volume : Measure V)) (p := (2 : ℝ≥0∞))
    simp_all only [Submodule.mem_bot]
  have hH_zero : H = 0 := by
    have h :=
      congrArg (fun G : Lp ℂ 2 (volume : Measure V) => 𝓕⁻ G)
        hFH_zero
    simpa using h
  have hH_zero_ae :
      ((H : Lp ℂ 2 (volume : Measure V)) : V -> ℂ)
        =ᵐ[(volume : Measure V)] fun _ => (0 : ℂ) := by
    rw [hH_zero]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure V)
  exact hH_coe.symm.trans hH_zero_ae
private lemma rankOneKernel_memLp_two
    {d : Nat} {f g : RealVec d -> ℂ}
    (hf : MemLp f 2 (volume : Measure (RealVec d)))
    (hg : MemLp g 2 (volume : Measure (RealVec d))) :
    MemLp (fun p : RealVec d × RealVec d => f p.1 * star (g p.2)) 2
      ((volume : Measure (RealVec d)).prod
        (volume : Measure (RealVec d))) := by
  have hint :
      Integrable
        (fun p : RealVec d × RealVec d =>
          ‖f p.1 * star (g p.2)‖ ^ 2)
        ((volume : Measure (RealVec d)).prod
          (volume : Measure (RealVec d))) := by
    have hf2 :
        Integrable (fun x => ‖f x‖ ^ 2)
          (volume : Measure (RealVec d)) := by
      simpa using hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hg2 :
        Integrable (fun y => ‖g y‖ ^ 2)
          (volume : Measure (RealVec d)) := by
      simpa using hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hprod :
        Integrable
          (fun p : RealVec d × RealVec d =>
            (‖f p.1‖ ^ 2) * (‖g p.2‖ ^ 2))
          ((volume : Measure (RealVec d)).prod
            (volume : Measure (RealVec d))) := by simpa using Integrable.mul_prod hf2 hg2
    convert hprod using 1 with p
    simp [mul_pow]
  have hmeas :
      AEStronglyMeasurable
        (fun p : RealVec d × RealVec d => f p.1 * star (g p.2))
        ((volume : Measure (RealVec d)).prod
          (volume : Measure (RealVec d))) := by
    exact
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
        ((hg.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd).star)
  exact
    (integrable_norm_rpow_iff
      (μ := (volume : Measure (RealVec d)).prod
        (volume : Measure (RealVec d)))
      (p := (2 : ℝ≥0∞)) hmeas (by norm_num) (by simp)).1
      (by simpa using hint)
private lemma shifted_conj_mul_integrable
    {d : Nat} {f g : RealVec d -> ℂ}
    (hf : MemLp f 2 (volume : Measure (RealVec d)))
    (hg : MemLp g 2 (volume : Measure (RealVec d)))
    (a b : RealVec d) :
    Integrable (fun t : RealVec d => f (t + a) * star (g (t + b)))
      (volume : Measure (RealVec d)) := by
  have hf_shift :
      MemLp (fun t : RealVec d => f (t + a)) 2
        (volume : Measure (RealVec d)) := by
    exact
      hf.comp_measurePreserving
        (MeasureTheory.measurePreserving_add_right
          (volume : Measure (RealVec d)) a)
  have hg_shift :
      MemLp (fun t : RealVec d => star (g (t + b))) 2
        (volume : Measure (RealVec d)) := by
    have hg0 :
        MemLp (fun t : RealVec d => g (t + b)) 2
          (volume : Measure (RealVec d)) := by
      exact
        hg.comp_measurePreserving
          (MeasureTheory.measurePreserving_add_right
            (volume : Measure (RealVec d)) b)
    exact hg0.star
  exact MemLp.integrable_mul hf_shift hg_shift
private lemma l2rep_ae_eq_coe
    {d : Nat} {f : L2Real d} {fRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) :
    ((f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(volume : Measure (RealVec d))] fRep := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  rw [← hf_eq]
  exact hf_mem.coeFn_toLp
private lemma centerKernel_memLp_two
    {d : Nat} {f : RealVec d -> ℂ}
    (hf : MemLp f 2 (volume : Measure (RealVec d))) :
    MemLp (fun p : PhaseSpace d =>
      f (p.2 + ((1 / 2 : ℝ) • p.1)) *
        star (f (p.2 - ((1 / 2 : ℝ) • p.1)))) 2
      (volume : Measure (PhaseSpace d)) := by
  let L := centerToEndpointsLinearEquiv d
  let μ : Measure (RealVec d) := volume
  let K : PhaseSpace d -> ℂ := fun p => f p.1 * star (f p.2)
  have hK : MemLp K 2 (μ.prod μ) := by
    exact
      (rankOneKernel_memLp_two (d := d) (f := f) (g := f) hf hf)
  have hdet : LinearMap.det (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d) ≠ 0 :=
    (LinearEquiv.isUnit_det' L).ne_zero
  have hmap :
      Measure.map (L : PhaseSpace d -> PhaseSpace d)
        (μ.prod μ) =
      ENNReal.ofReal
          |(LinearMap.det (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d))⁻¹| •
        (μ.prod μ) := by
    exact
      (MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
        (μ := μ.prod μ)
        (f := (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d)) hdet)
  have hK_map :
      MemLp K 2
        (Measure.map (L : PhaseSpace d -> PhaseSpace d)
          (μ.prod μ)) := by
    rw [hmap]
    exact hK.smul_measure (by simp)
  have hcomp :
      MemLp (K ∘ (L : PhaseSpace d -> PhaseSpace d)) 2
        (μ.prod μ) := by
    have hL_aemeasurable :
        AEMeasurable (L : PhaseSpace d -> PhaseSpace d)
          (μ.prod μ) :=
      (LinearMap.continuous_of_finiteDimensional
        (L : PhaseSpace d →ₗ[ℝ] PhaseSpace d)).measurable.aemeasurable
    exact hK_map.comp_of_map hL_aemeasurable
  exact
                                                hcomp
private lemma memLp_two_prod_right_ae
    {d : Nat} {F : PhaseSpace d -> ℂ}
    (hF : MemLp F 2 (volume : Measure (PhaseSpace d))) :
    ∀ᵐ x ∂(volume : Measure (RealVec d)),
      MemLp (fun t : RealVec d => F (x, t)) 2
        (volume : Measure (RealVec d)) := by
  let μ : Measure (RealVec d) := volume
  have hF_prod : MemLp F 2 (μ.prod μ) := by simpa [μ, MeasureTheory.Measure.volume_eq_prod] using hF
  have hmeas_sec :
      ∀ᵐ x ∂μ,
        AEStronglyMeasurable (fun t : RealVec d => F (x, t)) μ :=
    hF_prod.aestronglyMeasurable.prodMk_left
  have hint_global :
      Integrable (fun p : PhaseSpace d => ‖F p‖ ^ 2) (μ.prod μ) := by
    simpa using hF_prod.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hint_sec :
      ∀ᵐ x ∂μ,
        Integrable (fun t : RealVec d => ‖F (x, t)‖ ^ 2) μ := hint_global.prod_right_ae
  filter_upwards [hmeas_sec, hint_sec] with x hx_meas hx_int
  exact
    (integrable_norm_rpow_iff
      (μ := μ) (p := (2 : ℝ≥0∞)) hx_meas (by norm_num) (by simp)).1
      (by simpa using hx_int)
private lemma ae_prod_of_ae_ae_of_aestronglyMeasurable
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {F : α × β -> E}
    (hF_meas : AEStronglyMeasurable F (μ.prod ν))
    (hsec : ∀ᵐ x ∂μ, (fun y : β => F (x, y)) =ᵐ[ν] fun _ => (0 : E)) :
    F =ᵐ[μ.prod ν] fun _ => (0 : E) := by
  have hF_eq := hF_meas.aemeasurable.ae_eq_mk
  have hmeas_zero := hF_meas.aemeasurable.measurable_mk (measurableSet_singleton (0 : E))
  have hsections := MeasureTheory.Measure.ae_ae_of_ae_prod hF_eq
  refine hF_eq.trans ((MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas_zero).2 ?_)
  filter_upwards [hsec, hsections] with x hx hxm
  exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hxm) hx
private lemma sectionDiff_fourier_eq_ambiguity_sub
    {d : Nat} (f g : L2Real d) (x ω : RealVec d)
    (hf_int : Integrable (fun t : RealVec d =>
      ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((f : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))))
      (volume : Measure (RealVec d)))
    (hg_int : Integrable (fun t : RealVec d =>
      ((g : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))))
      (volume : Measure (RealVec d))) :
    (𝓕 (fun t : RealVec d =>
      ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((f : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))) -
      ((g : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
        star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x))))) ω =
      ambiguityRep f f (x, ω) - ambiguityRep g g (x, ω) := by
  let phase : RealVec d -> ℂ := fun t =>
    Complex.exp ((↑(-2 * Real.pi * ⟪t, ω⟫) * Complex.I))
  let Fsec : RealVec d -> ℂ := fun t =>
    ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
      star ((f : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x)))
  let Gsec : RealVec d -> ℂ := fun t =>
    ((g : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • x))) *
      star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • x)))
  have hFphase :
      Integrable (fun t : RealVec d => phase t * Fsec t)
        (volume : Measure (RealVec d)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (μ := (volume : Measure (RealVec d))) (f := Fsec) ω).2
        (by exact hf_int)
    simpa [phase, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul] using h
  have hGphase :
      Integrable (fun t : RealVec d => phase t * Gsec t)
        (volume : Measure (RealVec d)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (μ := (volume : Measure (RealVec d))) (f := Gsec) ω).2
        (by exact hg_int)
    simpa [phase, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul] using h
  rw [Real.fourier_eq']
  simp_rw [smul_eq_mul]
  change (∫ v : RealVec d, phase v * (Fsec v - Gsec v)) =
    ambiguityRep f f (x, ω) - ambiguityRep g g (x, ω)
  rw [show (fun v : RealVec d => phase v * (Fsec v - Gsec v)) =
    (fun v : RealVec d => phase v * Fsec v - phase v * Gsec v) by
      funext v
      ring]
  rw [integral_sub hFphase hGphase]
  have hphase_eq (t : RealVec d) :
      phase t = Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)) := by
    dsimp [phase]
    congr 1
    rw [real_inner_comm t ω]
    push_cast
    ring
  have hamb (h : L2Real d) :
      (∫ t : RealVec d, phase t *
        ((h : RealVec d → ℂ) (t + ((1 / 2 : ℝ) • x)) *
          star ((h : RealVec d → ℂ) (t - ((1 / 2 : ℝ) • x))))) =
        ambiguityRep h h (x, ω) := by
    rw [ambiguityRep]
    apply integral_congr_ae
    filter_upwards with t
    rw [hphase_eq]
    exact mul_comm _ _
  exact congrArg₂ (fun a b : ℂ => a - b) (hamb f) (hamb g)
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hAmb : ∀ ξ : PhaseSpace d, ambiguityRep f f ξ = ambiguityRep g g ξ) :
    (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d × RealVec d))]
        fun p => gRep p.1 * star (gRep p.2) := by
  let μ : Measure (RealVec d) := volume
  let f0 : RealVec d -> ℂ := (f : RealVec d -> ℂ)
  let g0 : RealVec d -> ℂ := (g : RealVec d -> ℂ)
  let centerDiff : PhaseSpace d -> ℂ := fun p =>
    f0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
        star (f0 (p.2 - ((1 / 2 : ℝ) • p.1))) -
      g0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
        star (g0 (p.2 - ((1 / 2 : ℝ) • p.1)))
  let endpointDiff : PhaseSpace d -> ℂ := fun p =>
    f0 p.1 * star (f0 p.2) - g0 p.1 * star (g0 p.2)
  have hf_mem : MemLp f0 2 μ := by exact MeasureTheory.Lp.memLp f
  have hg_mem : MemLp g0 2 μ := by exact MeasureTheory.Lp.memLp g
  have hf_center :
      MemLp (fun p : PhaseSpace d =>
        f0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
          star (f0 (p.2 - ((1 / 2 : ℝ) • p.1)))) 2
        (volume : Measure (PhaseSpace d)) := by
    exact centerKernel_memLp_two (d := d) hf_mem
  have hg_center :
      MemLp (fun p : PhaseSpace d =>
        g0 (p.2 + ((1 / 2 : ℝ) • p.1)) *
          star (g0 (p.2 - ((1 / 2 : ℝ) • p.1)))) 2
        (volume : Measure (PhaseSpace d)) := by
    exact centerKernel_memLp_two (d := d) hg_mem
  have hcenter_mem :
      MemLp centerDiff 2 (volume : Measure (PhaseSpace d)) := by
    refine MeasureTheory.MemLp.ae_eq ?_ (hf_center.sub hg_center)
    filter_upwards with p
    rfl
  have hcenter_sections :
      ∀ᵐ x ∂μ,
        MemLp (fun t : RealVec d => centerDiff (x, t)) 2 μ := by
    exact memLp_two_prod_right_ae (d := d) hcenter_mem
  have hcenter_zero_sections :
      ∀ᵐ x ∂μ,
        (fun t : RealVec d => centerDiff (x, t)) =ᵐ[μ] fun _ => (0 : ℂ) := by
    filter_upwards [hcenter_sections] with x hx_l2
    have hf_int :
        Integrable (fun t : RealVec d =>
          f0 (t + ((1 / 2 : ℝ) • x)) *
            star (f0 (t - ((1 / 2 : ℝ) • x))) ) μ := by
      refine (shifted_conj_mul_integrable (d := d) hf_mem hf_mem
          (((1 / 2 : ℝ) • x)) (-((1 / 2 : ℝ) • x))).congr ?_
      filter_upwards with t
      simp only [f0, sub_eq_add_neg]
    have hg_int :
        Integrable (fun t : RealVec d =>
          g0 (t + ((1 / 2 : ℝ) • x)) *
            star (g0 (t - ((1 / 2 : ℝ) • x))) ) μ := by
      refine (shifted_conj_mul_integrable (d := d) hg_mem hg_mem
          (((1 / 2 : ℝ) • x)) (-((1 / 2 : ℝ) • x))).congr ?_
      filter_upwards with t
      simp only [g0, sub_eq_add_neg]
    have hdiff_int :
        Integrable (fun t : RealVec d => centerDiff (x, t)) μ := by
      refine (hf_int.sub hg_int).congr ?_
      filter_upwards with t
      simp only [centerDiff, Pi.sub_apply, sub_eq_add_neg]
    have hfourier :
        ∀ ω : RealVec d,
          (𝓕 (fun t : RealVec d => centerDiff (x, t))) ω = 0 := by
      intro ω
      calc
        (𝓕 (fun t : RealVec d => centerDiff (x, t))) ω =
            ambiguityRep f f (x, ω) - ambiguityRep g g (x, ω) := by
              exact
                sectionDiff_fourier_eq_ambiguity_sub f g x ω
                  (by exact hf_int)
                  (by exact hg_int)
        _ = 0 := by
              simp_all only [Prod.forall, one_div, RCLike.star_def, sub_self]
    exact fourier_l1_l2_eq_zero_ae hdiff_int hx_l2 hfourier
  have hcenter_zero_prod :
      centerDiff =ᵐ[μ.prod μ] fun _ => (0 : ℂ) := by
    exact
      ae_prod_of_ae_ae_of_aestronglyMeasurable
        (by
          have hcenter_prod : MemLp centerDiff 2 (μ.prod μ) := by
            simpa [μ, MeasureTheory.Measure.volume_eq_prod] using hcenter_mem
          exact hcenter_prod.aestronglyMeasurable)
        hcenter_zero_sections
  have hendpoint_zero :
      endpointDiff =ᵐ[μ.prod μ] fun _ => (0 : ℂ) := by
    let L := centerToEndpointsLinearEquiv d
    have hdet_symm :
        LinearMap.det (L.symm : PhaseSpace d →ₗ[ℝ] PhaseSpace d) ≠ 0 :=
      (LinearEquiv.isUnit_det' L.symm).ne_zero
    have hqmp_symm :=
      MeasureTheory.Measure.LinearMap.quasiMeasurePreserving (μ.prod μ)
        (L.symm : PhaseSpace d →ₗ[ℝ] PhaseSpace d) hdet_symm
    have hcomp :=
      hqmp_symm.ae hcenter_zero_prod
    have hendpoint_eq : endpointDiff = fun p : PhaseSpace d => centerDiff (L.symm p) := by
      funext p
      have hplus :
          (2⁻¹ : ℝ) • p.1 + (2⁻¹ : ℝ) • p.2 +
              (2⁻¹ : ℝ) • (p.1 - p.2) = p.1 := by
        ext q
        simp
        ring
      have hminus :
          (2⁻¹ : ℝ) • p.1 + (2⁻¹ : ℝ) • p.2 -
              (2⁻¹ : ℝ) • (p.1 - p.2) = p.2 := by
        ext q
        simp
        ring
      simp [endpointDiff, centerDiff, L, centerToEndpointsLinearEquiv, hplus, hminus]
    filter_upwards [hcomp] with p hp
    simpa [hendpoint_eq] using hp
  have hf_ae : f0 =ᵐ[μ] fRep := by exact l2rep_ae_eq_coe hf_rep
  have hg_ae : g0 =ᵐ[μ] gRep := by exact l2rep_ae_eq_coe hg_rep
  have hendpoint_prod :
      endpointDiff =ᵐ[μ.prod μ] fun _ => (0 : ℂ) := by simpa using hendpoint_zero
  have hf_fst :
      (fun p : PhaseSpace d => f0 p.1)
        =ᵐ[μ.prod μ] fun p => fRep p.1 :=
    MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hf_ae
  have hf_snd :
      (fun p : PhaseSpace d => f0 p.2)
        =ᵐ[μ.prod μ] fun p => fRep p.2 :=
    MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hf_ae
  have hg_fst :
      (fun p : PhaseSpace d => g0 p.1)
        =ᵐ[μ.prod μ] fun p => gRep p.1 :=
    MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hg_ae
  have hg_snd :
      (fun p : PhaseSpace d => g0 p.2)
        =ᵐ[μ.prod μ] fun p => gRep p.2 :=
    MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hg_ae
  have hrep_prod :
      (fun p : PhaseSpace d => fRep p.1 * star (fRep p.2))
        =ᵐ[μ.prod μ] fun p => gRep p.1 * star (gRep p.2) := by
    filter_upwards [hendpoint_prod, hf_fst, hf_snd, hg_fst, hg_snd] with
      p hp hff hfs hgf hgs
    have h0 : f0 p.1 * star (f0 p.2) - g0 p.1 * star (g0 p.2) = 0 := hp
    have heq : f0 p.1 * star (f0 p.2) = g0 p.1 * star (g0 p.2) :=
      sub_eq_zero.mp h0
    simp_all only [Prod.forall, one_div, RCLike.star_def]
  simpa [μ, MeasureTheory.Measure.volume_eq_prod] using hrep_prod
end DimdPolyLEAN
