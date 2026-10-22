-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.moment_tax
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:52:25.04959+00:00
-- url     : https://prove2.me/submissions/8d52713d-c0a1-4493-8c74-e596aa0b505a

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting
set_option autoImplicit false
open ProbabilityTheory MeasureTheory
open CarbonPolicy.TaxVsCap

theorem kk_profit_q (b w γ a k : ℝ) (hb : 0 < b) :
    profit b w γ a k (qStar b γ a k) = (a - γ * k) ^ 2 / (4 * b) + w * k := by
  unfold profit qStar
  field_simp
  ring

theorem kk_int_sq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) (c : ℝ) :
    ∫ ω, (a ω - c) ^ 2 ∂P = Var[a; P] + (∫ ω, a ω ∂P - c) ^ 2 := by
  have h1 : Integrable a P := ha.integrable (by norm_num)
  have h2 : Integrable (fun ω => a ω ^ 2) P := ha.integrable_sq
  have hv := variance_eq_sub ha
  have e : ∀ ω, (a ω - c) ^ 2 = a ω ^ 2 - 2 * c * a ω + c ^ 2 := fun ω => by ring
  simp_rw [e]
  have h3 : Integrable (fun ω => 2 * c * a ω) P := h1.const_mul _
  have h4 : Integrable (fun ω => a ω ^ 2 - 2 * c * a ω) P := h2.sub h3
  rw [integral_add h4 (integrable_const _), integral_sub h2 h3, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hv' : Var[a; P] = ∫ ω, a ω ^ 2 ∂P - (∫ ω, a ω ∂P) ^ 2 := by
    rw [hv]; simp [Pi.pow_apply]
  rw [hv']
  ring

theorem kk_int_main {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) (c d b : ℝ) :
    ∫ ω, ((a ω - c) ^ 2 / (4 * b) + d) ∂P = (Var[a; P] + (∫ ω, a ω ∂P - c) ^ 2) / (4 * b) + d := by
  have hi : Integrable (fun ω => (a ω - c) ^ 2) P := (ha.sub (memLp_const c)).integrable_sq
  rw [integral_add (hi.div_const _) (integrable_const _), integral_div, kk_int_sq P a ha c]
  simp

theorem solution {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (γ : ℝ) :
    PiT M b β γp w γ =
      ((abar M.P M.a) - γ * (kbar M.P M.k)) ^ 2 / (4 * b) +
        (sigmaD M.P M.a) ^ 2 / (4 * b) - β * (γp - γ) ^ 2 + w * (kbar M.P M.k) := by
  haveI := M.prob
  unfold PiT
  simp_rw [kk_profit_q b w γ _ _ hb]
  have hs : sigmaD M.P M.a ^ 2 = Var[M.a; M.P] := by
    unfold sigmaD
    rw [Real.sq_sqrt (variance_nonneg _ _)]
  rw [hs, kk_int_main M.P M.a M.a_L2 (γ * kbar M.P M.k) (w * kbar M.P M.k) b]
  unfold abar
  ring
