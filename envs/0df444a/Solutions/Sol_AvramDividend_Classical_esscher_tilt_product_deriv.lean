-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilt_product_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:27:03.919982+00:00
-- url     : https://prove2.me/submissions/07da5ddb-7823-46ac-a563-ff4bffbb612f

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (θ a : ℝ) (G : ℝ → ℝ)
    (hG : DifferentiableAt ℝ G a) :
    deriv (fun x : ℝ => Real.exp (θ * x) * G x) a =
      Real.exp (θ * a) * (θ * G a + deriv G a) := by
  have hlin : HasDerivAt (fun x : ℝ => θ * x) θ a := by
    simpa using (hasDerivAt_id a).const_mul θ
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (θ * x))
      (Real.exp (θ * a) * θ) a :=
    (Real.hasDerivAt_exp (θ * a)).comp a hlin
  have hprod := hexp.mul hG.hasDerivAt
  have heq : deriv (fun x : ℝ => Real.exp (θ * x) * G x) a =
      (Real.exp (θ * a) * θ) * G a +
        Real.exp (θ * a) * deriv G a := hprod.deriv
  rw [heq]
  ring
