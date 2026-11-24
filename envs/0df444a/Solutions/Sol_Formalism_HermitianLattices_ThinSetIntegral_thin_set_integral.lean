-- Prove2me | solution 1 for Formalism.HermitianLattices.ThinSetIntegral.thin_set_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:34.473173+00:00
-- url     : https://prove2.me/submissions/17c5e4d8-8e8c-4d36-9a08-a53b1aa65c47

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TwistIsPrimitiveCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open DirichletCharacter
namespace Formalism.HermitianLattices.ThinSetIntegral
private lemma K_int (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (3 / 8 : ℝ))) (Set.Ioi 0) := by
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb
private lemma ptwise (c lam V v : ℝ) (hc : 0 < c) (hV : 1 ≤ V) (hl1 : 1 ≤ lam) (hl : lam ≤ V ^ (5 / 8 : ℝ))
    (hv : V < v) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) := by
  have hv1 : 1 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hV58 : V ^ (5 / 8 : ℝ) ≤ V := by
    have h := Real.rpow_le_rpow_of_exponent_le hV (show (5 / 8 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hlv : lam ≤ v := by linarith
  have h58 : lam ≤ v ^ (5 / 8 : ℝ) :=
    le_trans hl (Real.rpow_le_rpow (by linarith) hv.le (by norm_num))
  have hsq : Real.sqrt v ≤ v ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
  have hv58 : 0 < v ^ (5 / 8 : ℝ) := by positivity
  have hden : lam + Real.sqrt v ≤ 2 * v ^ (5 / 8 : ℝ) := by linarith
  have hdpos : 0 < lam + Real.sqrt v := by positivity
  have h38 : v ^ (3 / 8 : ℝ) = v / v ^ (5 / 8 : ℝ) := by
    rw [show (3 / 8 : ℝ) = 1 - 5 / 8 by norm_num, Real.rpow_sub hv0, Real.rpow_one]
  have h1 : c / 2 * v ^ (3 / 8 : ℝ) ≤ c * v / (lam + Real.sqrt v) := by
    rw [h38]
    calc c / 2 * (v / v ^ (5 / 8 : ℝ)) = c * v / (2 * v ^ (5 / 8 : ℝ)) := by
          field_simp
      _ ≤ c * v / (lam + Real.sqrt v) :=
          div_le_div_of_nonneg_left (by positivity) hdpos hden
  have h2 : V ^ (3 / 8 : ℝ) ≤ v ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hv.le (by norm_num)
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h3 : -c * v / (lam + Real.sqrt v) = -(c * v / (lam + Real.sqrt v)) := by ring
    rw [h3]
    nlinarith
  have hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [show (v ^ (2 : ℝ)) = v ^ 2 by norm_cast]
    nlinarith
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * (Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) :=
        mul_le_mul hpoly hexp (by positivity) (by positivity)
    _ = 4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) * (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ))) := by
        ring
private lemma half_rpow (y a : ℝ) (hy : 0 ≤ y) (ha1 : a ≤ 1) : y ^ a / 2 ≤ (y / 2) ^ a := by
  rw [Real.div_rpow hy (by norm_num)]
  have h2 : (2 : ℝ) ^ a ≤ 2 := by
    calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 2 := Real.rpow_one 2
  have hpos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy a) hpos h2
end Formalism.HermitianLattices.ThinSetIntegral
end

set_option autoImplicit false
open DirichletCharacter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ThinSetIntegral
namespace Formalism.HermitianLattices.ThinSetIntegral
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral := by
  intro ε c hε hc
  have hb : 0 < c / 4 := by positivity
  have hKi := K_int (c / 4) hb
  set g : ℝ → ℝ := fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (3 / 8 : ℝ)) with hg
  set K := ∫ v in Set.Ioi (0 : ℝ), g v with hK
  have E1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have E3 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2
  have E2a : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ (ε / 480)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < ε / 480 by positivity)).bound one_pos
  have E2b : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ (ε / 240) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 4
  have E4 : ∀ᶠ x : ℝ in Filter.atTop, 4 * K ≤ Real.exp (c / 16 * x ^ (ε / 8)) :=
    (Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (show 0 < ε / 8 by positivity)).const_mul_atTop
      (show 0 < c / 16 by positivity))).eventually_ge_atTop (4 * K)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (E1.and (E3.and (E2a.and (E2b.and E4))))
  refine ⟨c / 16, x₀, by positivity, ?_⟩
  intro x hx V lam hV hl1 hl
  obtain ⟨h1, h3, h2a, h2b, h4⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 ≤ x ^ (ε / 3) / 2 := by positivity

  have hlV : lam ≤ V ^ (5 / 8 : ℝ) := by
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg h1
    have hr0 : 0 < x ^ (ε / 480) := Real.rpow_pos_of_pos hx0 _
    have hlog : Real.log x ≤ x ^ (ε / 480) := by
      rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hr0.le, one_mul] at h2a
      exact h2a
    have hlog2 : Real.log x ^ 2 ≤ x ^ (ε / 240) := by
      have e : x ^ (ε / 240) = (x ^ (ε / 480)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
      rw [e]
      gcongr
    have e5 : (x ^ (ε / 3)) ^ (5 / 8 : ℝ) = x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240) := by
      rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have hh := half_rpow (x ^ (ε / 3)) (5 / 8) (by positivity) (by norm_num)
    have hm : (x ^ (ε / 3) / 2) ^ (5 / 8 : ℝ) ≤ V ^ (5 / 8 : ℝ) := Real.rpow_le_rpow hV0 hV (by norm_num)
    have ha : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hx0 _
    have hb' : 0 < x ^ (ε / 240) := Real.rpow_pos_of_pos hx0 _
    have s1 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240) := by gcongr
    have s2 : 2 * x ^ (ε / 5) * x ^ (ε / 240) * 4 ≤ 2 * x ^ (ε / 5) * x ^ (ε / 240) * x ^ (ε / 240) := by gcongr
    rw [e5] at hh
    linarith

  have hW : x ^ (ε / 8) / 2 ≤ V ^ (3 / 8 : ℝ) := by
    have e3 : (x ^ (ε / 3)) ^ (3 / 8 : ℝ) = x ^ (ε / 8) := by
      rw [← Real.rpow_mul hx0.le]; congr 1; ring
    have hh := half_rpow (x ^ (ε / 3)) (3 / 8) (by positivity) (by norm_num)
    have hm : (x ^ (ε / 3) / 2) ^ (3 / 8 : ℝ) ≤ V ^ (3 / 8 : ℝ) := Real.rpow_le_rpow hV0 hV (by norm_num)
    rw [e3] at hh
    linarith
  set A : ℝ := 4 * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤ A * g v :=
    fun v hv => ptwise c lam V v hc hV1 hl1 hlV hv
  have hgV : MeasureTheory.IntegrableOn (fun v => A * g v) (Set.Ioi V) :=
    (hKi.mono_set (Set.Ioi_subset_Ioi (by linarith))).const_mul A
  have hcont : Continuous (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) := by
    have hne : ∀ v : ℝ, lam + Real.sqrt v ≠ 0 := fun v => by
      have := Real.sqrt_nonneg v
      linarith
    fun_prop (disch := exact hne _)
  have hfi : MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgV hcont.aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt v hv
  refine ⟨hfi, ?_⟩
  have hg0 : ∀ v ∈ Set.Ioi (0 : ℝ), 0 ≤ g v := fun v hv => by
    have : (0 : ℝ) < v := hv
    simp only [hg]
    positivity
  have hK0 : 0 ≤ K := MeasureTheory.setIntegral_nonneg measurableSet_Ioi hg0
  have i1 : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      ∫ v in Set.Ioi V, A * g v := MeasureTheory.setIntegral_mono_on hfi hgV measurableSet_Ioi hpt
  have i2 : (∫ v in Set.Ioi V, A * g v) = A * ∫ v in Set.Ioi V, g v := MeasureTheory.integral_const_mul _ _
  have i3 : (∫ v in Set.Ioi V, g v) ≤ K :=
    MeasureTheory.setIntegral_mono_set hKi
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hg0))
      (Set.Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ V)).eventuallyLE
  have i4 : A * K ≤ Real.exp (-(c / 16) * x ^ (ε / 8)) := by
    have j1 : Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) ≤
        Real.exp (-(c / 16) * x ^ (ε / 8)) * Real.exp (-(c / 16 * x ^ (ε / 8))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have j2 : 4 * K * Real.exp (-(c / 16 * x ^ (ε / 8))) ≤ 1 := by
      rw [Real.exp_neg]
      have := Real.exp_pos (c / 16 * x ^ (ε / 8))
      rw [← div_eq_mul_inv, div_le_one this]
      exact h4
    have j3 := Real.exp_pos (-(c / 16) * x ^ (ε / 8))
    calc A * K = 4 * K * Real.exp (-(c / 4) * V ^ (3 / 8 : ℝ)) := by rw [hA]; ring
      _ ≤ 4 * K * (Real.exp (-(c / 16) * x ^ (ε / 8)) * Real.exp (-(c / 16 * x ^ (ε / 8)))) := by gcongr
      _ = Real.exp (-(c / 16) * x ^ (ε / 8)) * (4 * K * Real.exp (-(c / 16 * x ^ (ε / 8)))) := by ring
      _ ≤ Real.exp (-(c / 16) * x ^ (ε / 8)) * 1 := by gcongr
      _ = _ := mul_one _
  calc _ ≤ A * ∫ v in Set.Ioi V, g v := by rw [← i2]; exact i1
    _ ≤ A * K := by gcongr
    _ ≤ _ := i4
end Formalism.HermitianLattices.ThinSetIntegral
