-- Prove2me | solution 1 for CondConvexRisk.Entropic.rhoGamma_isCondConvexRiskMeasure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:46:11.971435+00:00
-- url     : https://prove2.me/submissions/c6b4ac5c-dcb4-4b3b-9e9e-71cb3a60209f

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem aux_egcc_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : MemLp X ⊤ P) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P, |X ω| ≤ C := by
  have hlt : eLpNormEssSup X P < ⊤ := by simpa [eLpNorm_exponent_top] using hX.2
  refine ⟨(eLpNormEssSup X P).toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := X) (μ := P)] with ω hω
  have := ENNReal.toReal_mono hlt.ne hω
  simpa using this

theorem aux_egcc_sm {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (X : Ω → ℝ) : StronglyMeasurable[m] (rhoGamma m P γ X) := by
  unfold rhoGamma
  exact ((Real.measurable_log.comp stronglyMeasurable_condExp.measurable).const_mul
    _).stronglyMeasurable

theorem aux_egcc_props {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (γ : ℝ) (hγ : 0 < γ)
    {X : Ω → ℝ} (hX : MemLp X ⊤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ Integrable (fun x => Real.exp (-γ * X x)) P ∧
      ∀ᵐ ω ∂P, |X ω| ≤ C ∧ 0 < (P[fun x => Real.exp (-γ * X x) | m]) ω ∧
        |rhoGamma m P γ X ω| ≤ C ∧
        Real.exp (γ * rhoGamma m P γ X ω) = (P[fun x => Real.exp (-γ * X x) | m]) ω := by
  obtain ⟨C, hC0, hC⟩ := aux_egcc_bound hX
  have hint : Integrable (fun x => Real.exp (-γ * X x)) P := by
    refine Integrable.of_bound ?_ (Real.exp (γ * C)) ?_
    · exact Real.continuous_exp.comp_aestronglyMeasurable (hX.1.const_mul (-γ))
    · filter_upwards [hC] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have := abs_le.1 hω
      nlinarith
  have h1 : P[fun _ => Real.exp (-(γ * C)) | m] ≤ᵐ[P] P[fun x => Real.exp (-γ * X x) | m] := by
    apply condExp_mono (integrable_const _) hint
    filter_upwards [hC] with ω hω
    show Real.exp (-(γ * C)) ≤ Real.exp (-γ * X ω)
    apply Real.exp_le_exp.2
    have := abs_le.1 hω
    nlinarith
  have h2 : P[fun x => Real.exp (-γ * X x) | m] ≤ᵐ[P] P[fun _ => Real.exp (γ * C) | m] := by
    apply condExp_mono hint (integrable_const _)
    filter_upwards [hC] with ω hω
    show Real.exp (-γ * X ω) ≤ Real.exp (γ * C)
    apply Real.exp_le_exp.2
    have := abs_le.1 hω
    nlinarith
  rw [condExp_const hm] at h1 h2
  refine ⟨C, hC0, hint, ?_⟩
  filter_upwards [h1, h2, hC] with ω h1 h2 hω
  have hpos : 0 < (P[fun x => Real.exp (-γ * X x) | m]) ω :=
    lt_of_lt_of_le (Real.exp_pos _) h1
  have hl1 : -(γ * C) ≤ Real.log ((P[fun x => Real.exp (-γ * X x) | m]) ω) := by
    rw [← Real.log_exp (-(γ * C))]
    exact Real.log_le_log (Real.exp_pos _) h1
  have hl2 : Real.log ((P[fun x => Real.exp (-γ * X x) | m]) ω) ≤ γ * C := by
    rw [← Real.log_exp (γ * C)]
    exact Real.log_le_log hpos h2
  refine ⟨hω, hpos, ?_, ?_⟩
  · unfold rhoGamma
    rw [abs_le]
    have hγi : 0 ≤ γ⁻¹ := inv_nonneg.2 hγ.le
    have e1 : γ⁻¹ * (γ * C) = C := by field_simp
    have e2 : γ⁻¹ * (-(γ * C)) = -C := by field_simp
    constructor
    · have := mul_le_mul_of_nonneg_left hl1 hγi
      linarith
    · have := mul_le_mul_of_nonneg_left hl2 hγi
      linarith
  · unfold rhoGamma
    rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul, Real.exp_log hpos]

end CondConvexRisk.Entropic

open CondConvexRisk.Entropic
open MeasureTheory

theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    IsCondConvexRiskMeasure m P (rhoGamma m P γ) := by
  refine
  { ae_congr := ?_
    stronglyMeasurable := ?_
    memLp := ?_
    translation := ?_
    monotone := ?_
    convex := ?_
    map_zero := ?_ }
  · intro X Y _ _ hXY
    have : (fun x => Real.exp (-γ * X x)) =ᵐ[P] (fun x => Real.exp (-γ * Y x)) := by
      filter_upwards [hXY] with ω hω
      rw [hω]
    filter_upwards [condExp_congr_ae (m := m) this] with ω hω
    simp only [rhoGamma, hω]
  · intro X _
    exact aux_egcc_sm m P γ X
  · intro X hX
    obtain ⟨C, _, _, hp⟩ := aux_egcc_props hm γ hγ hX
    refine memLp_top_of_bound ((aux_egcc_sm m P γ X).mono hm).aestronglyMeasurable C ?_
    filter_upwards [hp] with ω hω
    rw [Real.norm_eq_abs]
    exact hω.2.2.1
  · intro X Z hX hZ hZm
    obtain ⟨C, hC0, hint, hprops⟩ := aux_egcc_props hm γ hγ hX
    obtain ⟨D, hD0, hD⟩ := aux_egcc_bound hZ
    have hfun : (fun x => Real.exp (-γ * (X + Z) x)) =
        (fun x => Real.exp (-γ * Z x)) * (fun x => Real.exp (-γ * X x)) := by
      ext x
      simp only [Pi.add_apply, Pi.mul_apply, ← Real.exp_add]
      ring_nf
    have hsm : StronglyMeasurable[m] (fun x => Real.exp (-γ * Z x)) :=
      (Real.continuous_exp.measurable.comp (hZm.measurable.const_mul (-γ))).stronglyMeasurable
    have hpull := condExp_stronglyMeasurable_mul_of_bound hm hsm hint (Real.exp (γ * D)) (by
      filter_upwards [hD] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have := abs_le.1 hω
      nlinarith)
    filter_upwards [hpull, hprops] with ω h1 h2
    obtain ⟨_, hA, _, _⟩ := h2
    simp only [rhoGamma, hfun, h1, Pi.sub_apply]
    rw [Pi.mul_apply, Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp]
    field_simp
    ring
  · intro X Y hX hY hXY
    obtain ⟨C, _, hintX, hpX⟩ := aux_egcc_props hm γ hγ hX
    obtain ⟨D, _, hintY, hpY⟩ := aux_egcc_props hm γ hγ hY
    have hmono : P[fun x => Real.exp (-γ * Y x) | m] ≤ᵐ[P]
        P[fun x => Real.exp (-γ * X x) | m] := by
      apply condExp_mono hintY hintX
      filter_upwards [hXY] with ω hω
      exact Real.exp_le_exp.2 (by nlinarith)
    filter_upwards [hmono, hpX, hpY] with ω h hx hy
    unfold rhoGamma
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hy.2.1 h) (inv_nonneg.2 hγ.le)
  · intro X Y Λ hX hY hΛ hΛb
    obtain ⟨C, hC0, hintX, hpX⟩ := aux_egcc_props hm γ hγ hX
    obtain ⟨D, hD0, hintY, hpY⟩ := aux_egcc_props hm γ hγ hY
    have hWm : MemLp (Λ * X + (1 - Λ) * Y) ⊤ P := by
      refine memLp_top_of_bound ?_ (C + D) ?_
      · exact ((hΛ.mono hm).aestronglyMeasurable.mul hX.1).add
          (((stronglyMeasurable_const.sub hΛ).mono hm).aestronglyMeasurable.mul hY.1)
      · filter_upwards [hpX, hpY, hΛb] with ω hx hy hl
        have hx' := abs_le.1 hx.1
        have hy' := abs_le.1 hy.1
        simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Real.norm_eq_abs]
        rw [abs_le]
        constructor <;> nlinarith [hl.1, hl.2]
    obtain ⟨E, hE0, hintW, hpW⟩ := aux_egcc_props hm γ hγ hWm
    have hf := aux_egcc_sm m P γ X
    have hg := aux_egcc_sm m P γ Y
    have hk0 : StronglyMeasurable[m] (fun ω => Real.exp (-γ *
        (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω))) :=
      (Real.continuous_exp.measurable.comp (((hΛ.measurable.mul hf.measurable).add
        ((measurable_const.sub hΛ.measurable).mul hg.measurable)).const_mul (-γ))).stronglyMeasurable
    have hk1 : StronglyMeasurable[m] (fun ω => Λ ω * Real.exp (-γ * rhoGamma m P γ X ω)) :=
      (hΛ.measurable.mul (Real.continuous_exp.measurable.comp
        (hf.measurable.const_mul (-γ)))).stronglyMeasurable
    have hk2 : StronglyMeasurable[m] (fun ω => (1 - Λ ω) * Real.exp (-γ * rhoGamma m P γ Y ω)) :=
      ((measurable_const.sub hΛ.measurable).mul (Real.continuous_exp.measurable.comp
        (hg.measurable.const_mul (-γ)))).stronglyMeasurable
    have hb0 : ∀ᵐ ω ∂P, ‖Real.exp (-γ *
        (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω))‖ ≤ Real.exp (γ * (C + D)) := by
      filter_upwards [hpX, hpY, hΛb] with ω hx hy hl
      have hx' := abs_le.1 hx.2.2.1
      have hy' := abs_le.1 hy.2.2.1
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have h1 : -(C + D) ≤ Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω := by
        nlinarith [hl.1, hl.2]
      nlinarith
    have hb1 : ∀ᵐ ω ∂P, ‖Λ ω * Real.exp (-γ * rhoGamma m P γ X ω)‖ ≤ Real.exp (γ * C) := by
      filter_upwards [hpX, hΛb] with ω hx hl
      have hx' := abs_le.1 hx.2.2.1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl.1 (Real.exp_pos _).le)]
      have : Real.exp (-γ * rhoGamma m P γ X ω) ≤ Real.exp (γ * C) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith [Real.exp_pos (-γ * rhoGamma m P γ X ω), hl.1, hl.2]
    have hb2 : ∀ᵐ ω ∂P, ‖(1 - Λ ω) * Real.exp (-γ * rhoGamma m P γ Y ω)‖ ≤ Real.exp (γ * D) := by
      filter_upwards [hpY, hΛb] with ω hy hl
      have hy' := abs_le.1 hy.2.2.1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.2 hl.2) (Real.exp_pos _).le)]
      have : Real.exp (-γ * rhoGamma m P γ Y ω) ≤ Real.exp (γ * D) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith [Real.exp_pos (-γ * rhoGamma m P γ Y ω), hl.1, hl.2]
    have e0 := condExp_stronglyMeasurable_mul_of_bound hm hk0 hintW _ hb0
    have e1 := condExp_stronglyMeasurable_mul_of_bound hm hk1 hintX _ hb1
    have e2 := condExp_stronglyMeasurable_mul_of_bound hm hk2 hintY _ hb2
    have i0 : Integrable ((fun ω => Real.exp (-γ *
        (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω))) *
        fun x => Real.exp (-γ * (Λ * X + (1 - Λ) * Y) x)) P :=
      hintW.bdd_mul (hk0.mono hm).aestronglyMeasurable hb0
    have i1 : Integrable ((fun ω => Λ ω * Real.exp (-γ * rhoGamma m P γ X ω)) *
        fun x => Real.exp (-γ * X x)) P :=
      hintX.bdd_mul (hk1.mono hm).aestronglyMeasurable hb1
    have i2 : Integrable ((fun ω => (1 - Λ ω) * Real.exp (-γ * rhoGamma m P γ Y ω)) *
        fun x => Real.exp (-γ * Y x)) P :=
      hintY.bdd_mul (hk2.mono hm).aestronglyMeasurable hb2
    have eadd := condExp_add (m := m) i1 i2
    have hmono := condExp_mono (m := m) i0 (i1.add i2) (by
      filter_upwards [hΛb] with ω hl
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
      have hc := (convexOn_exp.2 (Set.mem_univ (-γ * rhoGamma m P γ X ω + -γ * X ω))
        (Set.mem_univ (-γ * rhoGamma m P γ Y ω + -γ * Y ω)) hl.1 (sub_nonneg.2 hl.2)
        (by ring))
      simp only [smul_eq_mul] at hc
      calc Real.exp (-γ * (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω)) *
            Real.exp (-γ * (Λ ω * X ω + (1 - Λ ω) * Y ω))
          = Real.exp (Λ ω * (-γ * rhoGamma m P γ X ω + -γ * X ω) +
              (1 - Λ ω) * (-γ * rhoGamma m P γ Y ω + -γ * Y ω)) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := hc
        _ = _ := by rw [Real.exp_add, Real.exp_add]; ring)
    filter_upwards [e0, e1, e2, eadd, hmono, hpX, hpY, hpW, hΛb] with
      ω h0 h1 h2 hadd hle hx hy hw hl
    rw [h0, hadd, Pi.add_apply, h1, h2] at hle
    simp only [Pi.mul_apply] at hle
    have ex : Real.exp (-γ * rhoGamma m P γ X ω) * (P[fun x => Real.exp (-γ * X x) | m]) ω = 1 := by
      rw [← hx.2.2.2, ← Real.exp_add]; simp
    have ey : Real.exp (-γ * rhoGamma m P γ Y ω) * (P[fun x => Real.exp (-γ * Y x) | m]) ω = 1 := by
      rw [← hy.2.2.2, ← Real.exp_add]; simp
    rw [← hw.2.2.2, mul_assoc, ex, mul_assoc, ey, ← Real.exp_add] at hle
    have hle' : -γ * (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω) +
        γ * rhoGamma m P γ (Λ * X + (1 - Λ) * Y) ω ≤ 0 := by
      have : Real.exp (-γ * (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω) +
        γ * rhoGamma m P γ (Λ * X + (1 - Λ) * Y) ω) ≤ Real.exp 0 := by
        rw [Real.exp_zero]; linarith
      exact Real.exp_le_exp.1 this
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
    nlinarith
  · filter_upwards with ω
    simp only [rhoGamma, Pi.zero_apply, mul_zero, Real.exp_zero, condExp_const hm, Real.log_one]
