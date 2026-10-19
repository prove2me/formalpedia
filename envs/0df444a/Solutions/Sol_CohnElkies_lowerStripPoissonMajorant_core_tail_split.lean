-- Prove2me | solution 1 for CohnElkies.lowerStripPoissonMajorant_core_tail_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/7838bb8e-0a23-4988-8a3e-41f753bfc373

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_integrable
import Theorems.Thm_CohnElkies_stripPoissonKernel_weighted_product_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaled_poisson_product_integrable
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_scaled_convolution
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_log_tail_simple

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) {c σ S : ℝ}
    (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1)
    (hS : 2 ≤ S) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
      (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
      (((d : ℝ) / 2) *
        Real.log ((8 * Real.pi * Real.exp 1 * c ^ 2) / S)) *
          stripPoissonCoreMass σ +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
  have hbelow : -1 < σ := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hSpos : 0 < S := by linarith
  let ℓ : ℝ := (d : ℝ) / 2
  let P : ℝ := 4 * Real.pi * Real.exp 1 * c ^ 2
  let A : ℝ := 8 * Real.pi * Real.exp 1 * c ^ 2
  let L : ℝ := ℓ * Real.log (A / S)
  let b : ℝ → ℝ := fun Y =>
    lowerGammaBoundaryLog ℓ (c * Real.sqrt d) (ℓ * Y)
  let p : ℝ → ℝ := lowerGammaScaledPositivePart d c
  have hP : 0 < P := by
    try dsimp [P]
    positivity
  have hA : A = 2 * P := by
    try dsimp [A, P]
    ring
  have hb_integrable : Integrable
      (fun T : ℝ => stripPoissonKernel σ T * b (S - T)) := by
    have hbase := lowerGammaScaled_poisson_product_integrable
      hdpos (R := c * Real.sqrt d) hbelow hσone S
    have hcomp := hbase.comp_sub_left S
    convert! hcomp using 1
    ext T
    try dsimp [b, ℓ]
    congr 1; ring_nf
  have hp_integrable : Integrable
      (fun T : ℝ => stripPoissonKernel σ T * p (S - T)) := by
    have hbase := stripPoissonKernel_weighted_product_integrable
      hbelow hσone
      (lowerGammaScaledPositivePart_integrable hd hc) S
    have hcomp := hbase.comp_sub_left S
    convert! hcomp using 1
    ext T
    try dsimp [p]
    congr 1; ring_nf
  have hcore_integrable : Integrable
      (fun T : ℝ =>
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T) := by
    have hbase :=
      ((stripPoissonKernel_integrable hbelow hσone).const_mul L).indicator
        (s := Icc (-1 : ℝ) 1) measurableSet_Icc
    convert! hbase using 1
    ext T
    by_cases hT : T ∈ Icc (-1 : ℝ) 1
    · simp [hT]
      ring
    · simp [hT]
  have hnear : ∀ T ∈ Icc (-1 : ℝ) 1, b (S - T) ≤ L := by
    intro T hT
    have hdiff : 0 < S - T := by linarith [hT.2]
    have hlarge : 1 ≤ |S - T| := by
      rw [abs_of_pos hdiff]
      linarith [hT.2]
    have hratio : P / |S - T| ≤ A / S := by
      apply (div_le_div_iff₀ (abs_pos.mpr hdiff.ne') hSpos).2
      rw [abs_of_pos hdiff, hA]
      nlinarith [mul_nonneg hP.le
        (show 0 ≤ S - 2 * T by linarith [hT.2])]
    have hlog : Real.log (P / |S - T|) ≤
        Real.log (A / S) := by
      apply Real.log_le_log (by positivity)
      exact hratio
    have htail :=
      lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
        hd hc hlarge
    change b (S - T) ≤ ℓ * Real.log (P / |S - T|) at htail
    change b (S - T) ≤ ℓ * Real.log (A / S)
    exact htail.trans
      (mul_le_mul_of_nonneg_left hlog hℓ.le)
  have hpointwise : ∀ T : ℝ,
      stripPoissonKernel σ T * b (S - T) ≤
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T +
          stripPoissonKernel σ T * p (S - T) := by
    intro T
    have hkernel := (stripPoissonKernel_pos hbelow hσone T).le
    have hpnonneg : 0 ≤ p (S - T) := by
      try dsimp [p, lowerGammaScaledPositivePart]
      exact le_max_right _ _
    have hb_le_p : b (S - T) ≤ p (S - T) := by
      try dsimp [b, p, ℓ, lowerGammaScaledPositivePart]
      exact le_max_left _ _
    by_cases hT : T ∈ Icc (-1 : ℝ) 1
    · simp only [Set.indicator_of_mem hT]
      have h := hnear T hT
      nlinarith [mul_nonneg hkernel hpnonneg,
        mul_nonneg hkernel (sub_nonneg.mpr h)]
    · simp only [Set.indicator_of_notMem hT, mul_zero,
        zero_add]
      exact mul_le_mul_of_nonneg_left hb_le_p hkernel
  have hcore_integral :
      (∫ T : ℝ,
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T) =
        L * stripPoissonCoreMass σ := by
    calc
      (∫ T : ℝ,
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T) =
        ∫ T : ℝ,
          (Icc (-1 : ℝ) 1).indicator
            (fun T => L * stripPoissonKernel σ T) T := by
          apply integral_congr_ae
          filter_upwards [] with T
          by_cases hT : T ∈ Icc (-1 : ℝ) 1
          · simp [hT]
            ring
          · simp [hT]
      _ = ∫ T in Icc (-1 : ℝ) 1,
        L * stripPoissonKernel σ T := by
        rw [integral_indicator measurableSet_Icc]
      _ = L * stripPoissonCoreMass σ := by
        rw [integral_const_mul]
        rfl
  have hpositive_integral :
      (∫ T : ℝ, stripPoissonKernel σ T * p (S - T)) =
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
    let f : ℝ → ℝ := fun T =>
      stripPoissonKernel σ T * p (S - T)
    calc
      (∫ T : ℝ, stripPoissonKernel σ T * p (S - T)) =
        ∫ T : ℝ, f T := by rfl
      _ = ∫ Y : ℝ, f (S - Y) :=
        (integral_sub_left_eq_self f volume S).symm
      _ = ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
        apply integral_congr_ae
        filter_upwards [] with Y
        try dsimp [f, p]
        congr 1
        ring_nf
  have hrepresentation :
      lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) =
        ∫ T : ℝ, stripPoissonKernel σ T * b (S - T) := by
    rw [lowerStripPoissonMajorant_scaled_convolution
      hℓ (c * Real.sqrt d) σ]
    have hscale : (((d : ℝ) / 2) * S / ((d : ℝ) / 2)) = S := by
      field_simp [hℓ.ne']
    rw [hscale]
    let f : ℝ → ℝ := fun T =>
      stripPoissonKernel σ T * b (S - T)
    calc
      (∫ Y : ℝ,
        stripPoissonKernel σ (S - Y) *
          lowerGammaBoundaryLog ((d : ℝ) / 2)
            (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) =
        ∫ Y : ℝ, f (S - Y) := by
          apply integral_congr_ae
          filter_upwards [] with Y
          try dsimp [f, b, ℓ]
          congr 1
          ring_nf
      _ = ∫ T : ℝ, f T :=
        integral_sub_left_eq_self f volume S
      _ = ∫ T : ℝ, stripPoissonKernel σ T * b (S - T) := by
        rfl
  rw [hrepresentation]
  calc
    (∫ T : ℝ, stripPoissonKernel σ T * b (S - T)) ≤
      ∫ T : ℝ,
        (stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T +
          stripPoissonKernel σ T * p (S - T)) := by
        apply integral_mono_ae hb_integrable
          (hcore_integrable.add hp_integrable)
        exact Filter.Eventually.of_forall hpointwise
    _ = L * stripPoissonCoreMass σ +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
      rw [integral_add hcore_integrable hp_integrable,
        hcore_integral, hpositive_integral]
    _ = (((d : ℝ) / 2) *
        Real.log ((8 * Real.pi * Real.exp 1 * c ^ 2) / S)) *
          stripPoissonCoreMass σ +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
      rfl
end CohnElkies
