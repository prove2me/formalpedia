-- Prove2me | solution 1 for ConnesGreen.energyGraph_no_derivative_only
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T03:20:46.812499+00:00
-- url     : https://prove2.me/submissions/48a702bd-c514-42a5-a4a2-db6728947c84

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical
noncomputable section
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

private theorem continuous_window_memLp (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (windowMeasure t) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc

private theorem supported_energyDomain (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    EnergyDomain t g :=
  ⟨continuous_window_memLp _ _ hg.1.1.continuous,
    continuous_window_memLp _ _ (hg.1.1.continuous_iteratedDeriv 1 (by simp))⟩

instance windowMeasure_finite (t : ℝ) : IsFiniteMeasure (windowMeasure t) := by
  unfold windowMeasure
  infer_instance

theorem windowL2_inner (t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure t)) (hg : MemLp g 2 (windowMeasure t)) :
    ⟪windowL2 t f, windowL2 t g⟫_ℂ =
      ∫ x, star (f x) * g x ∂windowMeasure t := by
  simp only [windowL2, dif_pos hf, dif_pos hg, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

/-- A smooth dual probe of the energy graph; this is not a replacement for
the original admissible-test class or a change to the physical carrier. -/
def derivativeProbe (t : ℝ) (φ : ℝ → ℂ) : Ambient t :=
  WithLp.toLp 2 (fun i : Fin 2 =>
    if i = 0 then windowL2 t φ else (2 : ℂ) • windowL2 t (iteratedDeriv 1 φ))

theorem supported_endpoints_zero (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    g t = 0 ∧ g (-t) = 0 := by
  constructor <;> by_contra hn
  · exact (lt_irrefl t) (hg.2 (subset_tsupport g hn)).2
  · exact (lt_irrefl (-t)) (hg.2 (subset_tsupport g hn)).1

theorem derivativeProbe_inner_energy (t : ℝ) (ht : 0 < t)
    (φ g : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hg : SupportedTest t g) :
    ⟪derivativeProbe t φ, energyVector t g⟫_ℂ = 0 := by
  have hφd : Continuous (iteratedDeriv 1 φ) :=
    hφ.continuous_iteratedDeriv 1 (by norm_num)
  have hgd : Continuous (iteratedDeriv 1 g) :=
    hg.1.1.continuous_iteratedDeriv 1 (by simp)
  have hφlp := continuous_window_memLp t φ hφ.continuous
  have hφdlp := continuous_window_memLp t _ hφd
  have hglp := (supported_energyDomain t g hg).1
  have hgdlp := (supported_energyDomain t g hg).2
  have hb := supported_endpoints_zero t g hg
  have hip := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := -t) (b := t) (u := fun x => star (φ x)) (v := g)
    (u' := fun x => star (iteratedDeriv 1 φ x)) (v' := iteratedDeriv 1 g)
    hφ.continuous.star.continuousOn hg.1.1.continuous.continuousOn
    (fun x _ => by simpa [iteratedDeriv_one] using
      (hφ.differentiable (by norm_num) x).hasDerivAt.star)
    (fun x _ => by simpa [iteratedDeriv_one] using
      (hg.1.1.differentiable (by simp) x).hasDerivAt)
    (hφd.star.intervalIntegrable _ _) (hgd.intervalIntegrable _ _)
  simp only [hb.1, hb.2, mul_zero, sub_zero] at hip
  have hi1 : Integrable (fun x => star (φ x) * iteratedDeriv 1 g x)
      (windowMeasure t) := (hφ.continuous.star.mul hgd).integrableOn_Icc
  have hi2 : Integrable (fun x => star (iteratedDeriv 1 φ x) * g x)
      (windowMeasure t) := (hφd.star.mul hg.1.1.continuous).integrableOn_Icc
  have hsum : (∫ x, star (φ x) * iteratedDeriv 1 g x +
      star (iteratedDeriv 1 φ x) * g x ∂windowMeasure t) = 0 := by
    unfold windowMeasure
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith : -t ≤ t)]
    convert hip using 1
    congr 1
    ext x
    ring
  have hinner : ⟪derivativeProbe t φ, energyVector t g⟫_ℂ =
      ⟪windowL2 t φ, windowL2 t (iteratedDeriv 1 g)⟫_ℂ +
      ⟪windowL2 t (iteratedDeriv 1 φ), windowL2 t g⟫_ℂ := by
    simp [derivativeProbe, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
      inner_smul_left, inner_smul_right, map_ofNat]
  rw [hinner, windowL2_inner t φ _ hφlp hgdlp,
    windowL2_inner t _ g hφdlp hglp, ← integral_add hi1 hi2]
  exact hsum

/-- Integration by parts is a closed linear constraint, so it survives the
span and completion in the exact published energySubspace definition. -/
theorem derivativeProbe_inner_physical (t : ℝ) (ht : 0 < t)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (h : Physical t) :
    ⟪derivativeProbe t φ, (h : Ambient t)⟫_ℂ = 0 := by
  let K : Submodule ℂ (Ambient t) := (ℂ ∙ derivativeProbe t φ)ᗮ
  have hs : energySubspace t ≤ K := by
    unfold energySubspace
    apply Submodule.topologicalClosure_minimal _ _
      (ℂ ∙ derivativeProbe t φ).isClosed_orthogonal
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr
      (derivativeProbe_inner_energy t ht φ g hφ hg)
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hs h.2)

/-- RG-1a closed on the prescribed carrier. Smooth probes are used only to
test the first coordinate; the physical carrier is never replaced. -/
theorem energyGraph_no_derivative_only (t : ℝ) (ht : 0 < t) :
    ∀ h : Physical t, (h : Ambient t) 1 = 0 → h = 0 := by
  intro h hh
  have hfirst : (h : Ambient t) 0 = 0 := by
    apply (SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := windowMeasure t)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).eq_zero_of_inner_right ℂ
    intro φ
    have hip := derivativeProbe_inner_physical t ht φ (φ.smooth 1) h
    have hlp : windowL2 t φ = φ.toLp 2 (windowMeasure t) := by
      simp only [windowL2, dif_pos (φ.memLp 2 (windowMeasure t)), SchwartzMap.toLp]
    simpa [derivativeProbe, PiLp.inner_apply, Fin.sum_univ_two, hh, hlp] using hip
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [hfirst, hh]

end ConnesGreen

theorem solution (t : ℝ) (ht : 0 < t) :
    ∀ h : ConnesGreen.Physical t, (h : ConnesGreen.Ambient t) 1 = 0 → h = 0 :=
  ConnesGreen.energyGraph_no_derivative_only t ht
