-- Prove2me | solution 1 for D1Bound5.pairIndependentBool_of_cached_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:00:56.868031+00:00
-- url     : https://prove2.me/submissions/89d8760a-7349-4ad9-bf2a-c28d4913a1ba

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Theorems.Thm_D1Bound5_pairCachedIndependentBool_sound

section
namespace D1Bound5

























/-- Existing two-color and full-ring graph consumers need no changes: the
cached certificate proves the exact old independent-class Boolean. -/
theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu))
    (cached : List (PairResidueVertex tau nu))
    (hcheck : pairCachedIndependentCertificateBool sieve vertices cached = true) :
    pairIndependentBool sieve vertices = true := by
  have hparts := Bool.and_eq_true_iff.mp hcheck
  have hcover : cached.map PairResidueVertex.vertex = vertices := of_decide_eq_true hparts.1
  have hrest := Bool.and_eq_true_iff.mp hparts.2
  have hvalid : ∀ x ∈ cached, x.signature = pairCoordinateSignature sieve x.vertex := by
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hrest.1 x hx)
  rw [← hcover]
  exact pairCachedIndependentBool_sound sieve cached hvalid hrest.2

end D1Bound5
end
