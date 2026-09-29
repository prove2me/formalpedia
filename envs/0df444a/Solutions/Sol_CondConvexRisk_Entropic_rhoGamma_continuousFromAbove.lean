-- Prove2me | solution 1 for CondConvexRisk.Entropic.rhoGamma_continuousFromAbove
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:11:09.933944+00:00
-- url     : https://prove2.me/submissions/44938788-aa66-48ad-a466-42bf9fcd2c7f

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

open Filter Topology in
theorem aux_rgcfa_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : MemLp X ⊤ P) : ∃ C : ℝ, ∀ᵐ ω ∂P, |X ω| ≤ C := by
  refine ⟨(eLpNorm X ⊤ P).toReal, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := X) (μ := P)] with ω hω
  rw [eLpNorm_exponent_top]
  have hne : eLpNormEssSup X P ≠ ⊤ := by
    have := hX.eLpNorm_ne_top
    rwa [eLpNorm_exponent_top] at this
  have h := ENNReal.toReal_mono hne hω
  simpa [Real.norm_eq_abs] using h

open Filter Topology in
theorem aux_rgcfa_main {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    IsContinuousFromAbove P (rhoGamma m P γ) := by
  intro X Y hX hY hXY
  set f : ℕ → Ω → ℝ := fun n x => Real.exp (-γ * X n x) with hf_def
  set g : Ω → ℝ := fun x => Real.exp (-γ * Y x) with hg_def
  have hYle : ∀ᵐ ω ∂P, ∀ n, Y ω ≤ X n ω := by
    filter_upwards [hXY] with ω hω n
    exact hω.1.le_of_tendsto hω.2 n
  obtain ⟨CY, hCY⟩ := aux_rgcfa_bound hY
  obtain ⟨C0, hC0⟩ := aux_rgcfa_bound (hX 0)
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) P := fun n =>
    Real.continuous_exp.comp_aestronglyMeasurable ((hX n).1.const_mul (-γ))
  have hg_meas : AEStronglyMeasurable g P :=
    Real.continuous_exp.comp_aestronglyMeasurable (hY.1.const_mul (-γ))
  have hfg : ∀ n, f n ≤ᵐ[P] g := fun n => by
    filter_upwards [hYle] with ω hω
    simp only [hf_def, hg_def]
    apply Real.exp_le_exp.mpr
    nlinarith [hω n]
  have hf_pos : ∀ n ω, 0 < f n ω := fun n ω => Real.exp_pos _
  have hg_bound : ∀ᵐ ω ∂P, ‖g ω‖ ≤ Real.exp (γ * CY) := by
    filter_upwards [hCY] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := neg_abs_le (Y ω)
    nlinarith
  have hg_int : Integrable g P := Integrable.of_bound hg_meas _ hg_bound
  have hf_bound : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ Real.exp (γ * CY) := fun n => by
    filter_upwards [hfg n, hg_bound] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_pos (hf_pos n ω)]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h2
    linarith
  have hf_int : ∀ n, Integrable (f n) P := fun n =>
    Integrable.of_bound (hf_meas n) _ (hf_bound n)
  have hf_mono : ∀ n, f n ≤ᵐ[P] f (n+1) := fun n => by
    filter_upwards [hXY] with ω hω
    simp only [hf_def]
    apply Real.exp_le_exp.mpr
    have := hω.1 (Nat.le_succ n)
    nlinarith
  set F : ℕ → Ω → ℝ := fun n => P[f n | m] with hF_def
  set G : Ω → ℝ := P[g | m] with hG_def
  have hF_mono : ∀ᵐ ω ∂P, Monotone (fun n => F n ω) := by
    have : ∀ᵐ ω ∂P, ∀ n, F n ω ≤ F (n+1) ω :=
      ae_all_iff.2 (fun n => condExp_mono (hf_int n) (hf_int (n+1)) (hf_mono n))
    filter_upwards [this] with ω hω
    exact monotone_nat_of_le_succ hω
  have hFG : ∀ᵐ ω ∂P, ∀ n, F n ω ≤ G ω :=
    ae_all_iff.2 (fun n => condExp_mono (hf_int n) hg_int (hfg n))
  set c : ℝ := Real.exp (-γ * C0) with hc_def
  have hc : 0 < c := Real.exp_pos _
  have hF0 : ∀ᵐ ω ∂P, c ≤ F 0 ω := by
    have h1 : (fun _ => c) ≤ᵐ[P] f 0 := by
      filter_upwards [hC0] with ω hω
      simp only [hf_def, hc_def]
      apply Real.exp_le_exp.mpr
      have := le_abs_self (X 0 ω)
      nlinarith
    have h2 := condExp_mono (m := m) (integrable_const c) (hf_int 0) h1
    rw [condExp_const hm c] at h2
    exact h2
  set L : Ω → ℝ := fun ω => ⨆ n, F n ω with hL_def
  have hFL : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hF_mono, hFG] with ω h1 h2
    exact tendsto_atTop_ciSup h1 ⟨G ω, by rintro _ ⟨n, rfl⟩; exact h2 n⟩
  have hLG : ∀ᵐ ω ∂P, L ω ≤ G ω := by
    filter_upwards [hFG] with ω h
    exact ciSup_le h
  have hF0L : ∀ᵐ ω ∂P, F 0 ω ≤ L ω := by
    filter_upwards [hF_mono, hFG] with ω h1 h2
    exact le_ciSup (f := fun n => F n ω) ⟨G ω, by rintro _ ⟨n, rfl⟩; exact h2 n⟩ 0
  have hL_meas : AEStronglyMeasurable L P :=
    aestronglyMeasurable_of_tendsto_ae _
      (fun n => (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable) hFL
  have hG_int : Integrable G P := integrable_condExp
  have hF_int : ∀ n, Integrable (F n) P := fun n => integrable_condExp
  have hL_int : Integrable L P := by
    refine Integrable.mono' ((hF_int 0).norm.add hG_int.norm) hL_meas ?_
    filter_upwards [hF0L, hLG] with ω h1 h2
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply, Real.norm_eq_abs]
    constructor
    · cases abs_cases (F 0 ω) <;> cases abs_cases (G ω) <;> linarith
    · cases abs_cases (F 0 ω) <;> cases abs_cases (G ω) <;> linarith
  have hGL_nonneg : 0 ≤ᵐ[P] (G - L) := by
    filter_upwards [hLG] with ω h
    simp only [Pi.zero_apply, Pi.sub_apply]
    linarith
  have h_int_le : ∀ n, ∫ ω, (G - L) ω ∂P ≤ ∫ ω, g ω ∂P - ∫ ω, f n ω ∂P := by
    intro n
    have : ∫ ω, (G - L) ω ∂P ≤ ∫ ω, (G - F n) ω ∂P := by
      apply integral_mono_ae (hG_int.sub hL_int) (hG_int.sub (hF_int n))
      filter_upwards [hFL, hF_mono] with ω h1 h2
      simp only [Pi.sub_apply]
      have := h2.ge_of_tendsto h1 n
      linarith
    rw [integral_sub' hG_int (hF_int n)] at this
    simp only [hG_def, hF_def] at this
    rw [integral_condExp hm, integral_condExp hm] at this
    exact this
  have h_tend : Tendsto (fun n => ∫ ω, g ω ∂P - ∫ ω, f n ω ∂P) atTop (𝓝 0) := by
    have : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, g ω ∂P)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (γ * CY)) hf_meas
        (integrable_const _) hf_bound
      filter_upwards [hXY] with ω hω
      exact (Real.continuous_exp.tendsto _).comp (hω.2.const_mul (-γ))
    have := (tendsto_const_nhds (x := ∫ ω, g ω ∂P)).sub this
    simpa using this
  have h_int_zero : ∫ ω, (G - L) ω ∂P = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' h_tend h_int_le
    · exact integral_nonneg_of_ae hGL_nonneg
  have hGL : G - L =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hGL_nonneg (hG_int.sub hL_int)).1 h_int_zero
  filter_upwards [hF_mono, hFL, hGL, hF0, hFG] with ω h1 h2 h3 h4 h5
  have hLeq : L ω = G ω := by
    simp only [Pi.sub_apply, Pi.zero_apply] at h3
    linarith
  have hpos : ∀ n, 0 < F n ω := fun n => lt_of_lt_of_le hc (h4.trans (h1 (Nat.zero_le n)))
  have hGpos : 0 < G ω := lt_of_lt_of_le (hpos 0) (h5 0)
  refine ⟨?_, ?_⟩
  · intro a b hab
    show γ⁻¹ * Real.log (F a ω) ≤ γ⁻¹ * Real.log (F b ω)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos a) (h1 hab)) (inv_nonneg.2 hγ.le)
  · show Tendsto (fun n => γ⁻¹ * Real.log (F n ω)) atTop (𝓝 (γ⁻¹ * Real.log (G ω)))
    rw [← hLeq] at hGpos ⊢
    exact (h2.log hGpos.ne').const_mul _

end CondConvexRisk.Entropic

open CondConvexRisk.Entropic
open MeasureTheory

theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    IsContinuousFromAbove P (rhoGamma m P γ) :=
  aux_rgcfa_main hm γ hγ
