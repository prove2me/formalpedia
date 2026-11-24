-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.gl2b2_thinIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:49.435954+00:00
-- url     : https://prove2.me/submissions/a66a556b-b961-430d-ab06-5c912339bf37

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterEstimateOfHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
private lemma gl2b2_intH (b : ℝ) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun v : ℝ => v ^ (2 : ℝ) * Real.exp (-b * v ^ (39 / 100 : ℝ)))
      (Set.Ioi 0) := by
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb
private lemma gl2b2_ptw (c v lam : ℝ) (hc : 0 < c) (hv : 1 ≤ v) (hl0 : 0 < lam)
    (hl : lam ≤ v ^ (61 / 100 : ℝ)) :
    (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by
  have hv0 : 0 < v := by linarith
  have h61 : v ^ (61 / 100 : ℝ) ≤ v := by
    calc v ^ (61 / 100 : ℝ) ≤ v ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
      _ = v := Real.rpow_one v
  have hlv : lam ≤ v := le_trans hl h61
  have hsq : Real.sqrt v ≤ v ^ (61 / 100 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hv (by norm_num)
  have hsplit : v ^ (39 / 100 : ℝ) * v ^ (61 / 100 : ℝ) = v := by
    rw [← Real.rpow_add hv0]; norm_num
  have hD : 0 < lam + Real.sqrt v := by positivity
  have h39 : 0 ≤ v ^ (39 / 100 : ℝ) := by positivity
  have hkey : v ^ (39 / 100 : ℝ) * (lam + Real.sqrt v) ≤ 2 * v := by
    nlinarith [mul_le_mul_of_nonneg_left hl h39, mul_le_mul_of_nonneg_left hsq h39]
  have hexp : Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left hkey hc.le]
  have hpoly : (v + lam) ^ 2 ≤ 4 * v ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlv) hv0.le, mul_nonneg (sub_nonneg.mpr hlv) hl0.le]
  calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
      ≤ (4 * v ^ (2 : ℝ)) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) :=
        mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
    _ = 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := by ring
private lemma gl2b2_big_lemma {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → M ≤ x ^ a := by
  refine ⟨max 1 (|M| ^ (1 / a)), le_max_left _ _, fun x hx => ?_⟩
  have h2 : |M| ^ (1 / a) ≤ x := le_trans (le_max_right _ _) hx
  have h3 : (|M| ^ (1 / a)) ^ a ≤ x ^ a :=
    Real.rpow_le_rpow (by positivity) h2 ha.le
  rw [← Real.rpow_mul (abs_nonneg M), one_div_mul_cancel ha.ne', Real.rpow_one] at h3
  exact le_trans (le_abs_self M) h3
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral
  intro ε c hε hc
  set I : ℝ := ∫ v in Set.Ioi 0, v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) with hI
  have hIint := gl2b2_intH (c / 4) (by positivity)
  have hI0 : 0 ≤ I := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro v hv
    have : 0 < v := hv
    positivity
  set δ : ℝ := 13 * ε / 20000 with hδ
  set δ' : ℝ := 13 * ε / 40000 with hδ'
  have hδpos : 0 < δ := by positivity
  have hδ'pos : 0 < δ' := by positivity
  obtain ⟨X1, -, hX1'⟩ := gl2b2_big_lemma (a := ε / 300) (by positivity) 2
  obtain ⟨X2, -, hX2'⟩ := gl2b2_big_lemma (a := ε / 8) (by positivity) (32 * I / c)
  obtain ⟨X3, -, hX3'⟩ := gl2b2_big_lemma (a := δ) hδpos (2 / δ' ^ 2)
  refine ⟨c / 8, max (max X1 X2) (max X3 2), by positivity, ?_⟩
  intro x hx V lam hV hlam1 hlam
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : (2:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hVx : x ^ (33 * ε / 100) ≤ V := by
    have h1 := hX1' x hx1
    have hs : x ^ (ε / 3) = x ^ (33 * ε / 100) * x ^ (ε / 300) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hpos : 0 ≤ x ^ (33 * ε / 100) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos]
  have hV1 : 1 ≤ V := le_trans (Real.one_le_rpow hxone (by positivity)) hVx
  have hV0 : 0 < V := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hLle : Real.log x ≤ x ^ δ' / δ' := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 δ')
    rw [Real.log_rpow hx0] at h
    rw [le_div_iff₀ hδ'pos]
    linarith
  have hL2 : Real.log x ^ 2 ≤ x ^ δ / δ' ^ 2 := by
    have hsq : x ^ δ = x ^ δ' * x ^ δ' := by
      rw [← Real.rpow_add hx0]; congr 1; rw [hδ, hδ']; ring
    have h2 : Real.log x ^ 2 ≤ (x ^ δ' / δ') ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLle) hL0.le,
        mul_nonneg (sub_nonneg.mpr hLle) (sub_nonneg.mpr hLle)]
    rw [hsq]
    calc Real.log x ^ 2 ≤ (x ^ δ' / δ') ^ 2 := h2
      _ = x ^ δ' * x ^ δ' / δ' ^ 2 := by ring
  have hlamV : lam ≤ V ^ (61 / 100 : ℝ) := by
    have h1 : (x ^ (33 * ε / 100)) ^ (61 / 100 : ℝ) ≤ V ^ (61 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hVx (by norm_num)
    rw [← Real.rpow_mul hx0.le] at h1
    have hs : x ^ (33 * ε / 100 * (61 / 100)) = x ^ (ε / 5) * x ^ δ * x ^ δ := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; rw [hδ]; ring
    rw [hs] at h1
    have h3 := hX3' x hx3
    have h4 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    have h5 : 2 * x ^ (ε / 5) * (x ^ δ / δ' ^ 2) = x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2) := by ring
    have h6 : x ^ (ε / 5) * x ^ δ * (2 / δ' ^ 2) ≤ x ^ (ε / 5) * x ^ δ * x ^ δ :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hpt : ∀ v ∈ Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) ≤
      4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
        (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ))) := by
    intro v hv
    have hv' : V < v := hv
    have hv1 : 1 ≤ v := by linarith
    have hlv : lam ≤ v ^ (61 / 100 : ℝ) :=
      le_trans hlamV (Real.rpow_le_rpow hV0.le hv'.le (by norm_num))
    have h1 := gl2b2_ptw c v lam hc hv1 (by linarith) hlv
    have h39 : V ^ (39 / 100 : ℝ) ≤ v ^ (39 / 100 : ℝ) :=
      Real.rpow_le_rpow hV0.le hv'.le (by norm_num)
    have h2 : Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ)) ≤
        Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left h39 hc.le]
    have hv2 : 0 ≤ v ^ (2 : ℝ) := by positivity
    calc (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))
        ≤ 4 * (v ^ (2 : ℝ) * Real.exp (-(c / 2) * v ^ (39 / 100 : ℝ))) := h1
      _ ≤ 4 * (v ^ (2 : ℝ) * (Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hv2) (by norm_num)
      _ = _ := by ring
  have hgint : MeasureTheory.IntegrableOn (fun v : ℝ => 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
      (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)))) (Set.Ioi V) :=
    (hIint.mono_set (Set.Ioi_subset_Ioi hV0.le)).const_mul _
  have hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
      (MeasureTheory.volume.restrict (Set.Ioi V)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hFint : MeasureTheory.IntegrableOn
      (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) := by
    refine MeasureTheory.Integrable.mono' hgint hFmeas ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt v hv
  refine ⟨hFint, ?_⟩
  have hw : x ^ (ε / 8) ≤ V ^ (39 / 100 : ℝ) := by
    have h1 : (x ^ (33 * ε / 100)) ^ (39 / 100 : ℝ) ≤ V ^ (39 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hVx (by norm_num)
    rw [← Real.rpow_mul hx0.le] at h1
    refine le_trans (Real.rpow_le_rpow_of_exponent_le hxone ?_) h1
    linarith
  have hInt_le : (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤
      4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := by
    calc (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
        ≤ ∫ v in Set.Ioi V, 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            (v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ))) :=
          MeasureTheory.setIntegral_mono_on hFint hgint measurableSet_Ioi hpt
      _ = 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) *
            ∫ v in Set.Ioi V, v ^ (2 : ℝ) * Real.exp (-(c / 4) * v ^ (39 / 100 : ℝ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hI]
          apply MeasureTheory.setIntegral_mono_set hIint
          · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
            intro v hv
            have : 0 < v := hv
            show (0:ℝ) ≤ _
            positivity
          · exact (Set.Ioi_subset_Ioi hV0.le).eventuallyLE
  have hw2 : 32 * I / c ≤ x ^ (ε / 8) := hX2' x hx2
  have h4I : 4 * I ≤ Real.exp (c / 8 * x ^ (ε / 8)) := by
    have h1 := Real.add_one_le_exp (c / 8 * x ^ (ε / 8))
    have h2 : 4 * I ≤ c / 8 * x ^ (ε / 8) := by
      rw [div_le_iff₀ hc] at hw2
      linarith
    linarith
  have hE1 : Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) ≤ Real.exp (-(c / 4) * x ^ (ε / 8)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hw hc.le]
  have hsplitE : Real.exp (-(c / 4) * x ^ (ε / 8)) =
      (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  calc (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)))
      ≤ 4 * Real.exp (-(c / 4) * V ^ (39 / 100 : ℝ)) * I := hInt_le
    _ ≤ 4 * Real.exp (-(c / 4) * x ^ (ε / 8)) * I :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE1 (by norm_num)) hI0
    _ = (4 * I) * (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ * Real.exp (-(c / 8) * x ^ (ε / 8)) := by
        rw [hsplitE]; ring
    _ ≤ Real.exp (c / 8 * x ^ (ε / 8)) * (Real.exp (c / 8 * x ^ (ε / 8)))⁻¹ *
          Real.exp (-(c / 8) * x ^ (ε / 8)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4I (by positivity))
          (Real.exp_pos _).le
    _ = Real.exp (-(c / 8) * x ^ (ε / 8)) := by
        rw [mul_inv_cancel₀ (Real.exp_pos _).ne']; ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
