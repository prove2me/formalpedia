-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_sum_special_positive_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:47.858573+00:00
-- url     : https://prove2.me/submissions/693193b2-66a5-4fea-ad68-e97ff79db3bb

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (q t a b : K) :
    ((1 - (1 : K)) / (q + 1) * finiteCore t a b t) * specialNormalizer t a b 1 = 0 := by
  simp
end FourierJacobi.Algebra
