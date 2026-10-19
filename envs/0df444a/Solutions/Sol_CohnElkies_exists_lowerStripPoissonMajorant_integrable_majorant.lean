-- Prove2me | solution 1 for CohnElkies.exists_lowerStripPoissonMajorant_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/ecf55e89-7a22-46f8-bc2b-99b7fca1a631

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_lowerStripPoissonMajorant_uniform_negative
import Theorems.Thm_CohnElkies_exists_lowerStripPoissonMajorant_logarithmic_tail

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
    {c : ℝ} (hc : 0 < c) (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ C : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ S : ℝ,
          Real.exp
            (lowerStripPoissonMajorant ((d : ℝ) / 2)
              (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
            C * Real.exp (-γ * ((d : ℝ) / 2)) /
              (1 + |S|) ^ 2 := by
  obtain ⟨σ, γ₀, hσpos, hσone, hγ₀, hcentral⟩ :=
    exists_lowerStripPoissonMajorant_uniform_negative hc hsharp
  obtain ⟨A, B, κ, hA, hB, hκ, htail⟩ :=
    exists_lowerStripPoissonMajorant_logarithmic_tail
      hc hσpos.le hσone
  let T : ℝ := max B (max A 1)
  let C : ℝ := max ((1 + T) ^ 2) (4 * A ^ 2)
  let γ : ℝ := γ₀ / 2
  have hT : 1 ≤ T := by
    try dsimp [T]
    exact le_trans (le_max_right A 1)
      (le_max_right B (max A 1))
  have hTA : A ≤ T := by
    try dsimp [T]
    exact le_trans (le_max_left A 1)
      (le_max_right B (max A 1))
  have hTB : B ≤ T := by
    try dsimp [T]
    exact le_max_left B (max A 1)
  have hC : 0 < C := by
    try dsimp [C]
    have hsq : 0 < (1 + T) ^ 2 := sq_pos_of_pos (by linarith)
    exact lt_of_lt_of_le hsq (le_max_left _ _)
  have hγ : 0 < γ := by
    try dsimp [γ]
    positivity
  have hscale : Tendsto
      (fun d : ℕ => (d : ℝ) / 2) atTop atTop := by
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hmul := hcast.atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert! hmul using 1
    ext d
    ring
  have hdimension : ∀ᶠ d : ℕ in atTop,
      4 / κ ≤ (d : ℝ) / 2 :=
    hscale.eventually (Ici_mem_atTop (4 / κ))
  refine ⟨σ, γ, C, hσpos, hσone, hγ, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hdimension, hcentral] with d hd hdim hcen
  intro S
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  by_cases hfar : T ≤ |S|
  · have hBS : B ≤ |S| := le_trans hTB hfar
    have hAS : A ≤ |S| := le_trans hTA hfar
    have habspos : 0 < |S| := lt_of_lt_of_le hA hAS
    have hratio : (1 : ℝ) ≤ |S| / A :=
      (le_div_iff₀ hA).2 (by simpa using! hAS)
    have hlog : 0 ≤ Real.log (|S| / A) :=
      Real.log_nonneg hratio
    have hκscale : 4 ≤ κ * ((d : ℝ) / 2) := by
      have h := (div_le_iff₀ hκ).1 hdim
      nlinarith
    have hnegative := hcen (((d : ℝ) / 2) * S)
    have hfrequency := htail d hd S hBS
    have haverage :
        lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
            -γ * ((d : ℝ) / 2) -
              2 * Real.log (|S| / A) := by
      try dsimp [γ]
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hκscale) hlog]
    have hpow :
        Real.exp (-(2 : ℝ) * Real.log (|S| / A)) =
          (A / |S|) ^ 2 := by
      calc
        Real.exp (-(2 : ℝ) * Real.log (|S| / A)) =
            Real.exp
              (-Real.log (|S| / A) +
                -Real.log (|S| / A)) := by
              congr 1
              ring
        _ = Real.exp (-Real.log (|S| / A)) *
              Real.exp (-Real.log (|S| / A)) := by
              rw [Real.exp_add]
        _ = (A / |S|) ^ 2 := by
              rw [Real.exp_neg, Real.exp_log
                (div_pos habspos hA)]
              field_simp [habspos.ne', hA.ne']
    have hu : 1 ≤ |S| := le_trans hT hfar
    have hquad :
        (1 + |S|) ^ 2 ≤ 4 * |S| ^ 2 := by
      nlinarith [sq_nonneg (|S| - 1)]
    have hquadmajor :
        (A / |S|) ^ 2 * (1 + |S|) ^ 2 ≤
          4 * A ^ 2 := by
      calc
        (A / |S|) ^ 2 * (1 + |S|) ^ 2 ≤
            (A / |S|) ^ 2 * (4 * |S| ^ 2) :=
              mul_le_mul_of_nonneg_left hquad (sq_nonneg _)
        _ = 4 * A ^ 2 := by
              field_simp [habspos.ne']
    have hden : 0 < (1 + |S|) ^ 2 :=
      sq_pos_of_pos (by positivity)
    have hprofile :
        (A / |S|) ^ 2 ≤ C / (1 + |S|) ^ 2 := by
      apply (le_div_iff₀ hden).2
      exact hquadmajor.trans
        (show 4 * A ^ 2 ≤ C from le_max_right _ _)
    calc
      Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
        Real.exp
          (-γ * ((d : ℝ) / 2) -
            2 * Real.log (|S| / A)) :=
          Real.exp_le_exp.mpr haverage
      _ = Real.exp (-γ * ((d : ℝ) / 2)) *
          (A / |S|) ^ 2 := by
        rw [show -γ * ((d : ℝ) / 2) -
          2 * Real.log (|S| / A) =
            -γ * ((d : ℝ) / 2) +
              (-(2 : ℝ) * Real.log (|S| / A)) by ring,
            Real.exp_add, hpow]
      _ ≤ Real.exp (-γ * ((d : ℝ) / 2)) *
          (C / (1 + |S|) ^ 2) :=
        mul_le_mul_of_nonneg_left hprofile
          (Real.exp_pos _).le
      _ = C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2 := by
        ring
  · have hnear : |S| ≤ T := le_of_lt (lt_of_not_ge hfar)
    have hden : 0 < (1 + |S|) ^ 2 :=
      sq_pos_of_pos (by positivity)
    have hnearquad : (1 + |S|) ^ 2 ≤ (1 + T) ^ 2 := by
      nlinarith [abs_nonneg S]
    have hdenmajor : (1 + |S|) ^ 2 ≤ C :=
      hnearquad.trans (le_max_left _ _)
    have hexpcentral :
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
          Real.exp (-γ * ((d : ℝ) / 2)) := by
      apply Real.exp_le_exp.mpr
      have h := hcen (((d : ℝ) / 2) * S)
      try dsimp [γ]
      nlinarith [mul_nonneg hγ₀.le hℓ.le]
    calc
      Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
        Real.exp (-γ * ((d : ℝ) / 2)) := hexpcentral
      _ ≤ C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2 := by
        apply (le_div_iff₀ hden).2
        calc
          Real.exp (-γ * ((d : ℝ) / 2)) *
              (1 + |S|) ^ 2 ≤
            Real.exp (-γ * ((d : ℝ) / 2)) * C :=
              mul_le_mul_of_nonneg_left hdenmajor
                (Real.exp_pos _).le
          _ = C * Real.exp (-γ * ((d : ℝ) / 2)) := by
            ring
end CohnElkies
