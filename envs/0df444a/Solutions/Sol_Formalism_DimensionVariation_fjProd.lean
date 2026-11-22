-- Prove2me | solution 1 for Formalism.DimensionVariation.fjProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:41.457246+00:00
-- url     : https://prove2.me/submissions/abe46ebc-4af2-4fef-b99b-d4d681abccfc

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {κ : Type} [Fintype κ] (a b : κ → ℕ) (u : κ → ℂ) :
    mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ) = ∏ x, fjW (a x) (b x) (u x) := by
  simp only [mono, cj, nsq, fjW, ← Finset.sum_neg_distrib,
    Real.exp_sum, Complex.ofReal_prod, Finset.prod_mul_distrib]
end Formalism.DimensionVariation
