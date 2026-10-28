-- Prove2me | solution 1 for D1Bound5.pairIndependentBool_of_light_selected_floor_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:46:04.789349+00:00
-- url     : https://prove2.me/submissions/dda84b91-1dc0-4420-a096-b12aebe9539b

import Init
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
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions
import Theorems.Thm_D1Bound5_pairIndependentBool_of_cached_certificate
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentCertificateBool_eq_raw
import Theorems.Thm_D1Bound5_pairRawSelectedFloorIndependentBool_eq
import Theorems.Thm_D1Bound5_pairSelectedFloorIndependentCertificateBool_sound

section
namespace D1Bound5
open QuadInt













/-- The final assertion is the unchanged independent-class Boolean. The
selected tags, floor values, signatures, and vertex coverage are all checked. -/
theorem pairIndependentBool_of_selected_floor_certificate {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ))
    (hcheck : pairSelectedFloorIndependentCertificateBool sieve vertices cached rows = true) :
    pairIndependentBool sieve vertices = true :=
  pairIndependentBool_of_cached_certificate sieve vertices cached
    (pairSelectedFloorIndependentCertificateBool_sound hd sieve vertices cached rows hcheck)

end D1Bound5
end

section
namespace D1Bound5















theorem pairRawSelectedFloorIndependentCertificateBool_eq {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu))
    (cached : List (PairResidueVertex tau nu)) (rows : List (ℕ × List ℕ)) :
    pairRawSelectedFloorIndependentCertificateBool sieve vertices cached rows =
      pairSelectedFloorIndependentCertificateBool sieve vertices cached rows := by
  simp only [pairRawSelectedFloorIndependentCertificateBool,
    pairSelectedFloorIndependentCertificateBool, pairRawSelectedFloorIndependentBool_eq]

/-- Reuse the accepted selected-certificate soundness theorem through exact
Boolean equality. No new mask or arithmetic hypothesis is introduced. -/
theorem pairIndependentBool_of_raw_selected_floor_certificate {tau nu : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ))
    (hcheck : pairRawSelectedFloorIndependentCertificateBool sieve vertices cached rows = true) :
    pairIndependentBool sieve vertices = true :=
  pairIndependentBool_of_selected_floor_certificate hd sieve vertices cached rows
    ((pairRawSelectedFloorIndependentCertificateBool_eq sieve vertices cached rows).symm.trans hcheck)

end D1Bound5
end

section
namespace D1Bound5







































/-- Mathematical soundness is reused from the accepted checker only after
the unconditional Boolean identity. Positive discriminant is exactly the
original soundness premise and is not needed for the computation equality. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ))
    (hcheck : pairLightSelectedFloorIndependentCertificateBool tau nu sieve
      (vertices.map pairLightCoordinates) (cached.map pairLightCachedCoordinates) rows = true) :
    pairIndependentBool sieve vertices = true :=
  pairIndependentBool_of_raw_selected_floor_certificate hd sieve vertices cached rows
    ((pairLightSelectedFloorIndependentCertificateBool_eq_raw sieve vertices cached rows).symm.trans hcheck)

end D1Bound5
end
