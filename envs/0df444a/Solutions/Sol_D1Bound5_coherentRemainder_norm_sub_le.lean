-- Prove2me | solution 1 for D1Bound5.coherentRemainder_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:34.647066+00:00
-- url     : https://prove2.me/submissions/ec53e6b5-90f1-4ea1-a074-5c358eec96bc

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
import Theorems.Thm_D1Bound5_coherent_half_binomial_manuscript_tail_norm_le

section
open Finset

namespace D1Bound5





/-- The manuscript tail estimate applied directly to the remainder in
the actual coherent form. -/
theorem _root_.solution
    {m : ℕ} (a : Fin m → ℂ) (hm : 2 ≤ m) (p q : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P) (ha : ∀ i, A ≤ ‖a i‖)
    (hp : ‖p⁻¹‖ ≤ 1 / P) (hq : ‖q⁻¹‖ ≤ 1 / P) (hAP : 1 < A * P) :
    ‖coherentRemainder a p q - halfBinomialWeightedCoeff p⁻¹ q⁻¹ m‖ ≤
      (4 * |halfBinomialCoeff (m + 1)|) / P ^ m *
        (1 / (1 - 1 / (A * P)) ^ m - 1) := by
  have hs : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have h := coherent_half_binomial_manuscript_tail_norm_le Finset.univ a hs
    p⁻¹ q⁻¹ A P hA hP (fun i _ => ha i) hp hq hAP
  simpa only [Finset.card_univ, Fintype.card_fin, coherentRemainder] using h.2



end D1Bound5
end
