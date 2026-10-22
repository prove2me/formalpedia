-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.emission_difference
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:51:51.229191+00:00
-- url     : https://prove2.me/submissions/24ba28c2-67a0-4042-be9a-c4b73238ddc0

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting
set_option autoImplicit false
open ProbabilityTheory MeasureTheory
open CarbonPolicy.TaxVsCap

theorem solution {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b γT γC : ℝ) (hb : 0 < b) :
    ST M b γT - SC M b γC =
      (γT - γC) * ((abar M.P M.a) - (γT + γC) * (kbar M.P M.k)) / (2 * b) := by
  haveI := M.prob
  have i1 : Integrable M.a M.P := M.a_L2.integrable (by norm_num)
  have i2 : Integrable M.k M.P := M.k_L2.integrable (by norm_num)
  unfold CarbonPolicy.TaxVsCap.ST CarbonPolicy.TaxVsCap.SC qStar
  have e1 : ∀ ω, γT * ((M.a ω - γT * kbar M.P M.k) / (2 * b)) =
      (γT / (2 * b)) * M.a ω - γT ^ 2 * kbar M.P M.k / (2 * b) := fun ω => by
    field_simp
  have e2 : ∀ ω, γC * ((M.a ω - γC * M.k ω) / (2 * b)) =
      (γC / (2 * b)) * M.a ω - (γC ^ 2 / (2 * b)) * M.k ω := fun ω => by
    field_simp
  simp_rw [e1, e2]
  rw [integral_sub (i1.const_mul _) (integrable_const _),
    integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold abar kbar
  field_simp
  ring
