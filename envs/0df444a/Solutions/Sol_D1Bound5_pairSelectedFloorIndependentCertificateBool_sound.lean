-- Prove2me | solution 1 for D1Bound5.pairSelectedFloorIndependentCertificateBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:18:14.921317+00:00
-- url     : https://prove2.me/submissions/785c2530-34d0-4ac1-827b-39772eb32e5c

import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions
import Theorems.Thm_D1Bound5_pairSelectedFloorIndependentBool_sound

section
namespace D1Bound5
open QuadInt











theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ))
    (hcheck : pairSelectedFloorIndependentCertificateBool sieve vertices cached rows = true) :
    pairCachedIndependentCertificateBool sieve vertices cached = true := by
  have hparts := Bool.and_eq_true_iff.mp hcheck
  have hrest := Bool.and_eq_true_iff.mp hparts.2
  apply Bool.and_eq_true_iff.mpr
  exact ⟨hparts.1, Bool.and_eq_true_iff.mpr
    ⟨hrest.1, pairSelectedFloorIndependentBool_sound hd sieve cached rows hrest.2⟩⟩



end D1Bound5
end
