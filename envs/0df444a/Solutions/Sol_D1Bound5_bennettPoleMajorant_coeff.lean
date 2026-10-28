-- Prove2me | solution 1 for D1Bound5.bennettPoleMajorant_coeff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:48:49.700178+00:00
-- url     : https://prove2.me/submissions/fb945ed1-f30d-4201-9d34-9e075527b9a5

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettPositiveSeries_Definitions

section
open Finset

namespace D1Bound5



@[simp] theorem _root_.solution (d : ℝ) (p n : ℕ) :
    PowerSeries.coeff n (bennettPoleMajorant d p) =
      |Ring.choose (-(p : ℝ)) n| * (d⁻¹) ^ (p + n) := by
  exact PowerSeries.coeff_mk _ _

















end D1Bound5
end
