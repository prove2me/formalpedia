-- Prove2me | solution 1 for FaulhuberTFA.crossAmbiguity_eq_stft
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:10:47.623178+00:00
-- url     : https://prove2.me/submissions/f423e649-f54d-4ba3-b8be-d5e41b8de291

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace
open FaulhuberTFA

private lemma ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem solution {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω : Rd d) :
    crossAmbiguity f g x ω = Complex.exp (Real.pi * Complex.I * (⟪x, ω⟫_ℝ : ℂ)) * stft g f x ω := by
  unfold crossAmbiguity stft
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (μ := volume) _ (-((1 / 2 : ℝ) • x))]
  congr 1; funext t
  have h1 : t + -((1 / 2 : ℝ) • x) + (1 / 2 : ℝ) • x = t := by abel
  have h2 : t + -((1 / 2 : ℝ) • x) - (1 / 2 : ℝ) • x = t - x := by
    rw [sub_eq_add_neg, add_assoc, ← neg_add, ← add_smul]; norm_num; rw [← sub_eq_add_neg]
  rw [h1, h2]
  have h3 : -⟪ω, t + -((1 / 2 : ℝ) • x)⟫_ℝ = (1/2) * ⟪x, ω⟫_ℝ + -⟪ω, t⟫_ℝ := by
    simp only [inner_add_right, inner_neg_right, inner_smul_right, real_inner_comm x ω]; ring
  rw [h3, ePhase_add]
  have h4 : ePhase ((1/2) * ⟪x, ω⟫_ℝ) = Complex.exp (Real.pi * Complex.I * (⟪x, ω⟫_ℝ : ℂ)) := by
    unfold ePhase; congr 1; push_cast; ring
  rw [h4]; ring
