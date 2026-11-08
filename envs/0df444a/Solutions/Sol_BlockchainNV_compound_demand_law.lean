-- Prove2me | solution 1 for BlockchainNV.compound_demand_law
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:25:31.788696+00:00
-- url     : https://prove2.me/submissions/7ab5911c-3887-4a6f-887a-90defca56af0

import Mathlib
import Definitions.Def_BlockchainNV_Params
import Definitions.Def_BlockchainNV_IsModel

open MeasureTheory ProbabilityTheory

open BlockchainNV in
theorem solution (θ : Params) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X ε : Ω → ℝ} (hM : IsModel θ P X ε) :
    HasLaw (fun ω => θ.lam + θ.beta * X ω + ε ω)
      (gaussianReal (θ.lam + θ.beta * θ.muX)
        (θ.beta ^ 2 * θ.sigmaX ^ 2 + θ.sigma ^ 2).toNNReal) P := by
  obtain ⟨hX, hε, hind⟩ := hM
  have hY := gaussianReal_const_add (gaussianReal_const_mul hX θ.beta) θ.lam
  have hind' : IndepFun (fun ω => θ.lam + θ.beta * X ω) ε P :=
    hind.comp (measurable_const.add (measurable_const.mul measurable_id)) measurable_id
  have hS := hind'.hasLaw_fun_add hY hε
  rw [gaussianReal_conv_gaussianReal] at hS
  convert hS using 2
  · first | ring | (symm; ring)
  · apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal']
    rw [max_eq_left (by positivity : (0 : ℝ) ≤ θ.beta ^ 2 * θ.sigmaX ^ 2 + θ.sigma ^ 2),
      max_eq_left (sq_nonneg θ.sigmaX), max_eq_left (sq_nonneg θ.sigma)]
