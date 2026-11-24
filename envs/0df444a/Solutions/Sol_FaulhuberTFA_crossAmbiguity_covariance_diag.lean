-- Prove2me | solution 1 for FaulhuberTFA.crossAmbiguity_covariance_diag
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:13:55.443402+00:00
-- url     : https://prove2.me/submissions/4f39f408-26b1-42ee-a43f-be3f5312ccb4

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace
open FaulhuberTFA

private lemma ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma conj_ePhase (s : ℝ) : starRingEnd ℂ (ePhase s) = ePhase (-s) := by
  unfold ePhase; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

theorem solution {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω ξ η : Rd d) :
    crossAmbiguity (modul η (transl ξ f)) (modul η (transl ξ g)) x ω =
      ePhase (⟪x, η⟫_ℝ - ⟪ω, ξ⟫_ℝ) * crossAmbiguity f g x ω := by
  unfold crossAmbiguity modul transl
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (μ := volume) _ ξ]
  congr 1; funext t
  have h1 : t + ξ + (1 / 2 : ℝ) • x - ξ = t + (1 / 2 : ℝ) • x := by abel
  have h2 : t + ξ - (1 / 2 : ℝ) • x - ξ = t - (1 / 2 : ℝ) • x := by abel
  rw [h1, h2, map_mul, conj_ePhase]
  have h3 : ⟪η, t + ξ + (1 / 2 : ℝ) • x⟫_ℝ + -⟪η, t + ξ - (1 / 2 : ℝ) • x⟫_ℝ + -⟪ω, t + ξ⟫_ℝ
      = (⟪x, η⟫_ℝ - ⟪ω, ξ⟫_ℝ) + -⟪ω, t⟫_ℝ := by
    simp only [inner_add_right, inner_sub_right, inner_smul_right, real_inner_comm x]
    ring
  have : ePhase ⟪η, t + ξ + (1 / 2 : ℝ) • x⟫_ℝ * f (t + (1 / 2 : ℝ) • x) *
        (ePhase (-⟪η, t + ξ - (1 / 2 : ℝ) • x⟫_ℝ) * starRingEnd ℂ (g (t - (1 / 2 : ℝ) • x))) *
        ePhase (-⟪ω, t + ξ⟫_ℝ)
      = ePhase (⟪η, t + ξ + (1 / 2 : ℝ) • x⟫_ℝ + -⟪η, t + ξ - (1 / 2 : ℝ) • x⟫_ℝ + -⟪ω, t + ξ⟫_ℝ)
        * (f (t + (1 / 2 : ℝ) • x) * starRingEnd ℂ (g (t - (1 / 2 : ℝ) • x))) := by
    rw [ePhase_add, ePhase_add]; ring
  rw [this, h3, ePhase_add]; ring
