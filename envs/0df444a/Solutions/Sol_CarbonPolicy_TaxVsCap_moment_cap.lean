-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.moment_cap
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:52:53.591705+00:00
-- url     : https://prove2.me/submissions/6966760c-ff53-41dd-9305-2122991b95ec

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

theorem kk_var_eq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) :
    Var[a; P] = ∫ ω, a ω ^ 2 ∂P - (∫ ω, a ω ∂P) ^ 2 := by
  rw [variance_eq_sub ha]; simp [Pi.pow_apply]

theorem solution {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (γ : ℝ) :
    PiC M b β γp w γ =
      ((abar M.P M.a) - γ * (kbar M.P M.k)) ^ 2 / (4 * b) +
        (sigmaD M.P M.a) ^ 2 / (4 * b) +
        (γ ^ 2 * (sigma M.P M.k) ^ 2 - 2 * γ * (rho M.P M.a M.k) *
          (sigmaD M.P M.a) * (sigma M.P M.k)) / (4 * b) -
        β * (γp - γ) ^ 2 + w * (kbar M.P M.k) := by
  haveI := M.prob
  have ha := M.a_L2
  have hk := M.k_L2
  unfold PiC
  simp_rw [kk_profit_q b w γ _ _ hb]
  have hs : sigmaD M.P M.a ^ 2 = Var[M.a; M.P] := by
    unfold sigmaD
    rw [Real.sq_sqrt (variance_nonneg _ _)]
  have hs2 : sigma M.P M.k ^ 2 = Var[M.k; M.P] := by
    unfold sigma
    rw [Real.sq_sqrt (variance_nonneg _ _)]
  have hpos : 0 < sigmaD M.P M.a * sigma M.P M.k := by
    apply mul_pos
    · unfold sigmaD; exact Real.sqrt_pos.2 M.var_a_pos
    · unfold sigma; exact Real.sqrt_pos.2 M.var_k_pos
  have hrho : rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k = cov[M.a, M.k; M.P] := by
    unfold rho
    rw [mul_assoc, div_mul_cancel₀ _ hpos.ne']
  have i1 : Integrable M.a M.P := ha.integrable (by norm_num)
  have i2 : Integrable M.k M.P := hk.integrable (by norm_num)
  have ia2 : Integrable (fun ω => M.a ω ^ 2) M.P := ha.integrable_sq
  have ik2 : Integrable (fun ω => M.k ω ^ 2) M.P := hk.integrable_sq
  have iak : Integrable (fun ω => M.a ω * M.k ω) M.P := ha.integrable_mul hk
  have e : ∀ ω, (M.a ω - γ * M.k ω) ^ 2 =
      M.a ω ^ 2 - 2 * γ * (M.a ω * M.k ω) + γ ^ 2 * M.k ω ^ 2 := fun ω => by ring
  have hint : ∫ ω, (M.a ω - γ * M.k ω) ^ 2 ∂M.P =
      ∫ ω, M.a ω ^ 2 ∂M.P - 2 * γ * ∫ ω, M.a ω * M.k ω ∂M.P + γ ^ 2 * ∫ ω, M.k ω ^ 2 ∂M.P := by
    simp_rw [e]
    have h3 : Integrable (fun ω => 2 * γ * (M.a ω * M.k ω)) M.P := iak.const_mul _
    have h4 : Integrable (fun ω => γ ^ 2 * M.k ω ^ 2) M.P := ik2.const_mul _
    have h34 : Integrable (fun ω => M.a ω ^ 2 - 2 * γ * (M.a ω * M.k ω)) M.P := ia2.sub h3
    rw [integral_add h34 h4, integral_sub ia2 h3, integral_const_mul, integral_const_mul]
  have hq : Integrable (fun ω => (M.a ω - γ * M.k ω) ^ 2) M.P :=
    (ha.sub (hk.const_mul γ)).integrable_sq
  have hcov : cov[M.a, M.k; M.P] = ∫ ω, M.a ω * M.k ω ∂M.P - abar M.P M.a * kbar M.P M.k := by
    rw [covariance_eq_sub ha hk]; rfl
  have hr2 : 2 * γ * rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k =
      2 * γ * cov[M.a, M.k; M.P] := by rw [← hrho]; ring
  rw [integral_add (hq.div_const _) (i2.const_mul w), integral_div, hint, integral_const_mul,
    hs, hs2, hr2, hcov, kk_var_eq M.P M.a ha, kk_var_eq M.P M.k hk]
  unfold abar kbar
  field_simp
  ring
