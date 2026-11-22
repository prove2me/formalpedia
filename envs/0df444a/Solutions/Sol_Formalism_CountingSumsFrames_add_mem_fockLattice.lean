-- Prove2me | solution 1 for Formalism.CountingSumsFrames.add_mem_fockLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:33.819834+00:00
-- url     : https://prove2.me/submissions/23d556e5-5fe6-4da1-aa77-15a18300d4c2

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
theorem _root_.solution (R : Subring K) (f g : PolXY K k) (hf : f ∈ FockLat R) (hg : g ∈ FockLat R) :
    f + g ∈ FockLat R := by
  intro m
  rw [coeff_add, mul_add]
  exact R.add_mem (hf m) (hg m)
end Formalism.CountingSumsFrames
