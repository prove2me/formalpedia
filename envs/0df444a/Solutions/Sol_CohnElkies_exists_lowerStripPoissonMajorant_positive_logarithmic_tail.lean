-- Prove2me | solution 1 for CohnElkies.exists_lowerStripPoissonMajorant_positive_logarithmic_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/e4b98780-417b-4696-bfe8-6ef76108d6e5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_pos
import Theorems.Thm_CohnElkies_exists_lowerGammaScaledPositivePart_uniform_bound
import Theorems.Thm_CohnElkies_stripPoissonCoreMass_pos
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_poisson_exponential_tail
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_core_tail_split

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
    {c σ : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧
      ∀ d : ℕ, 2 ≤ d →
        ∀ S : ℝ, B ≤ S →
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
              -κ * ((d : ℝ) / 2) * Real.log (S / A) := by
  have hbelow : -1 < σ := by linarith
  obtain ⟨C, hC, huniform⟩ :=
    exists_lowerGammaScaledPositivePart_uniform_bound hc
  let A : ℝ := 8 * Real.pi * Real.exp 1 * c ^ 2
  let m : ℝ := stripPoissonCoreMass σ
  let κ : ℝ := m / 2
  let a : ℝ := Real.pi / 2
  let β : ℝ := stripBottomMass σ * a * C
  have hA : 0 < A := by
    try dsimp [A]
    positivity
  have hm : 0 < m :=
    stripPoissonCoreMass_pos hbelow hσone
  have hκ : 0 < κ := by
    try dsimp [κ]
    positivity
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hβ : 0 < β := by
    try dsimp [β]
    exact mul_pos
      (mul_pos (stripBottomMass_pos hσone) ha) hC
  have hscale : Tendsto
      (fun S : ℝ => S * a) atTop atTop :=
    tendsto_id.atTop_mul_const ha
  have hnegative : Tendsto
      (fun S : ℝ => -(S * a)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hscale
  have hexponential : Tendsto
      (fun S : ℝ => Real.exp (-(S * a))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hdecay : Tendsto
      (fun S : ℝ => β * Real.exp (-a * (S - C)))
        atTop (𝓝 0) := by
    have hmul :=
      hexponential.const_mul (β * Real.exp (a * C))
    convert! hmul using 1
    · ext S
      calc
        β * Real.exp (-a * (S - C)) =
            β * Real.exp (a * C + -(S * a)) := by
              congr 1
              ring_nf
        _ = β * (Real.exp (a * C) *
              Real.exp (-(S * a))) := by
              rw [Real.exp_add]
        _ = β * Real.exp (a * C) *
              Real.exp (-(S * a)) := by
              ring
    · simp
  have hsmall : ∀ᶠ S : ℝ in atTop,
      β * Real.exp (-a * (S - C)) < m / 4 :=
    hdecay.eventually
      (Iio_mem_nhds (by positivity : 0 < m / 4))
  have hbounded : ∀ᶠ S : ℝ in atTop,
      max 2 (max C (2 * A)) ≤ S :=
    eventually_ge_atTop _
  obtain ⟨B₀, hB₀⟩ :=
    Filter.eventually_atTop.1 (hsmall.and hbounded)
  let B : ℝ := max 1 B₀
  have hB : 0 < B := by
    try dsimp [B]
    linarith [le_max_left (1 : ℝ) B₀]
  refine ⟨A, B, κ, hA, hB, hκ, ?_⟩
  intro d hd S hSB
  have hBzero : B₀ ≤ S :=
    le_trans (le_max_right 1 B₀) hSB
  obtain ⟨hsmallS, hlargeS⟩ := hB₀ S hBzero
  have hStwo : 2 ≤ S :=
    le_trans (le_max_left 2 _) hlargeS
  have hSC : C ≤ S :=
    le_trans (le_trans (le_max_left C (2 * A))
      (le_max_right 2 _)) hlargeS
  have hSratio : 2 * A ≤ S :=
    le_trans (le_trans (le_max_right C (2 * A))
      (le_max_right 2 _)) hlargeS
  have hSpos : 0 < S := by linarith
  obtain ⟨hsupport, hpositive⟩ := huniform d hd
  have htail := lowerStripPoissonMajorant_core_tail_split
    hd hc hσ hσone hStwo
  have hpositive_tail := lowerGammaScaledPositivePart_poisson_exponential_tail
    hd hc hσ hσone hC hsupport hpositive hSC
  have hpositive_bound :
      (∫ Y : ℝ,
        stripPoissonKernel σ (S - Y) *
          lowerGammaScaledPositivePart d c Y) ≤
        (β * Real.exp (-a * (S - C))) *
          ((d : ℝ) / 2) := by
    calc
      (∫ Y : ℝ,
        stripPoissonKernel σ (S - Y) *
          lowerGammaScaledPositivePart d c Y) ≤
        (stripBottomMass σ * (Real.pi / 2) *
          Real.exp (-(Real.pi / 2) * (S - C))) *
            (C * ((d : ℝ) / 2)) := hpositive_tail
      _ = (β * Real.exp (-a * (S - C))) *
          ((d : ℝ) / 2) := by
        try dsimp [β, a]
        ring
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hratio : (2 : ℝ) ≤ S / A :=
    (le_div_iff₀ hA).2 hSratio
  have hlogratio : (1 / 2 : ℝ) ≤ Real.log (S / A) :=
    hlogtwo.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio)
  have hflip : Real.log (A / S) = -Real.log (S / A) := by
    rw [Real.log_div hA.ne' hSpos.ne',
      Real.log_div hSpos.ne' hA.ne']
    ring
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  calc
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
      (((d : ℝ) / 2) * Real.log (A / S)) * m +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
        exact htail
    _ ≤ (((d : ℝ) / 2) * Real.log (A / S)) * m +
        (β * Real.exp (-a * (S - C))) *
          ((d : ℝ) / 2) := by
      linarith [hpositive_bound]
    _ ≤ -κ * ((d : ℝ) / 2) * Real.log (S / A) := by
      rw [hflip]
      try dsimp [κ]
      nlinarith [mul_nonneg
        (show 0 ≤ (d : ℝ) / 2 by positivity)
        (show 0 ≤ m * Real.log (S / A) / 2 -
          β * Real.exp (-a * (S - C)) by
          nlinarith [mul_nonneg hm.le
            (show 0 ≤ Real.log (S / A) - 1 / 2 by linarith)])]
end CohnElkies
