-- Prove2me | solution 1 for Formalism.CountingSumsFrames.smul_mem_fockLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:57.683797+00:00
-- url     : https://prove2.me/submissions/6236cccd-5ec7-454e-b083-847ac8808f32

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (R : Subring K) (r : K) (hr : r ∈ R) (f : PolXY K k) (hf : f ∈ FockLat R) :
    r • f ∈ FockLat R := by
  intro m
  rw [coeff_smul, smul_eq_mul, mul_left_comm]
  exact R.mul_mem hr (hf m)
end Formalism.CountingSumsFrames
