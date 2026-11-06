-- Prove2me | solution 1 for FalconerPath.quantitative_bad_directions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-11-05T23:15:25.790204+00:00
-- url     : https://prove2.me/submissions/694c2a9b-ef18-4a3f-bced-29bfddaf2a91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FalconerPath_defs
import Mathlib
import Theorems.Thm_OAI_Falconer_linear_projection_gain
import Theorems.Thm_FalconerPath_direction_law_on_sphere
import Theorems.Thm_FalconerPath_bad_direction_grid_incidence

noncomputable section
set_option autoImplicit false
open FalconerPath
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem solution {k : ℕ} (hk : 2 ≤ k) (q t ζ L C : ℝ)
    (hq : (k:ℝ)-1 ≤ q) (hqS : q ≤ (k:ℝ)-1/2)
    (ht : (k:ℝ)-1/2 < t) (htk : t < k)
    (hζ : 0 < ζ) (hL : 0 < L) (hC : 0 < C) :
    ∃ c₁ ε₁ δ₀ : ℝ, 0 < c₁ ∧ 0 < ε₁ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ μ : Measure (Space (k+1)),
        Probability μ → Carried μ (Metric.closedBall 0 L) →
        ballBound μ t (δ^(-ε₁)) δ →
        ∃ Bplus : Set (Space (k+1)), MeasurableSet Bplus ∧ Bplus ⊆ unitSphere (k+1) ∧
          badDirections μ L C δ q c₁ ⊆ Bplus ∧
          ∀ lam : Measure (Space (k+1)), Subprobability lam →
            Carried lam (unitSphere (k+1)) → capBound lam q (δ^(-ε₁)) δ →
            (q = (k:ℝ)-1 → plateBound lam ζ (δ^(-ε₁)) δ) →
            lam Bplus ≤ ENNReal.ofReal (δ^c₁) := by
  obtain ⟨ε, hε, c, hc, δstar, hδstar, gain⟩ :=
    OAI.Falconer.linear_projection_gain k hk q t hq hqS ht htk
      (C+1) (by linarith) L hL.le ζ (fun _ => hζ)
  let c₁ := min (ε/4) (c/4)
  have hc₁ : 0 < c₁ := lt_min (by positivity) (by positivity)
  have hcε : c₁ ≤ ε := (min_le_left _ _).trans (by linarith)
  have hcc : 2*c₁ ≤ c := by have := min_le_right (ε/4) (c/4); dsimp [c₁]; linarith
  refine ⟨c₁, ε/2, min 1 (δstar/2), hc₁, by positivity,
    lt_min zero_lt_one (by positivity), min_le_left _ _, ?_⟩
  intro δ hδ hsmall μ hμ hcar hball
  have hδ1 : δ ≤ 1 := hsmall.trans (min_le_left _ _)
  have hδstar' : δ < δstar := by
    have := hsmall.trans (min_le_right 1 (δstar/2)); linarith
  have hloss : δ^(-(ε/2)) ≤ δ^(-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  obtain ⟨Bplus, hB, hBsphere, hbad, E, hE, hcover, hlower⟩ :=
    FalconerPath.bad_direction_grid_incidence L C δ q c₁ hL hC hδ hδ1 hc₁ μ hμ hcar
  refine ⟨Bplus, hB, hBsphere, hbad, ?_⟩
  intro lam hlam hlcar hlcap hlplate
  have hcapε : capBound lam q (δ^(-ε)) δ := by
    intro w hw r hr hδr hr1
    exact (hlcap w hw r hr hδr hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg hr.le _)))
  have hplateε : q = (k:ℝ)-1 → plateBound lam ζ (δ^(-ε)) δ := by
    intro heq w hw r hr hδr hr1
    exact (hlplate heq w hw r hr hδr hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg hr.le _)))
  obtain ⟨ν, hν, hνcap, hνplate, hνB⟩ :=
    FalconerPath.direction_law_on_sphere hk lam q ζ (δ^(-ε)) δ hδ hlam hlcar hcapε hplateε
  have hgain := gain δ hδ hδstar' μ ν hμ.le hν
    (by
      filter_upwards [ae_iff.mpr hcar] with x hx
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    (fun x r hr hr1 => (hball x r (hδ.trans_le hr) hr hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss
        (Real.rpow_nonneg (hδ.trans_le hr).le _)))) hνcap hνplate
    E hE.nullMeasurableSet (by
      intro w
      obtain ⟨anchors, hcount, hanchors⟩ := hcover w
      exact ⟨anchors, hcount.trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)), hanchors⟩)
  have hmass := (hlower ν hν).trans hgain
  rw [hνB Bplus hB hBsphere] at hmass
  have hpow : δ^c ≤ δ^(c₁+c₁) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hmass' : ENNReal.ofReal (δ^c₁) * lam Bplus ≤
      ENNReal.ofReal (δ^c₁) * ENNReal.ofReal (δ^c₁) := by
    calc
      _ ≤ ENNReal.ofReal (δ^c) := hmass
      _ ≤ ENNReal.ofReal (δ^(c₁+c₁)) := ENNReal.ofReal_le_ofReal hpow
      _ = _ := by rw [Real.rpow_add hδ, ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (δ^c₁) ≠ 0)
    ENNReal.ofReal_ne_top).mp hmass'
