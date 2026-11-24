-- Prove2me | solution 1 for FaulhuberTFA.stft_covariance
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:12:32.122798+00:00
-- url     : https://prove2.me/submissions/e7004455-06b4-49fb-b17c-24a562f53148

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace
open FaulhuberTFA

private lemma ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem solution {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ξ ω η : Rd d) :
    stft g (modul η (transl ξ f)) x ω = ePhase (-⟪ξ, ω - η⟫_ℝ) * stft g f (x - ξ) (ω - η) := by
  unfold stft modul transl
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (μ := volume) _ ξ]
  congr 1; funext t
  have h1 : t + ξ - ξ = t := by abel
  have h2 : t + ξ - x = t - (x - ξ) := by abel
  rw [h1, h2]
  have h3 : ⟪η, t + ξ⟫_ℝ + -⟪ω, t + ξ⟫_ℝ = -⟪ξ, ω - η⟫_ℝ + -⟪ω - η, t⟫_ℝ := by
    simp only [inner_add_right, inner_sub_right, real_inner_comm ξ, real_inner_comm t]
    ring
  have : ePhase ⟪η, t + ξ⟫_ℝ * f t * starRingEnd ℂ (g (t - (x - ξ))) * ePhase (-⟪ω, t + ξ⟫_ℝ)
      = ePhase (⟪η, t + ξ⟫_ℝ + -⟪ω, t + ξ⟫_ℝ) * (f t * starRingEnd ℂ (g (t - (x - ξ)))) := by
    rw [ePhase_add]; ring
  rw [this, h3, ePhase_add]; ring
