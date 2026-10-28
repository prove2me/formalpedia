-- Prove2me | solution 1 for D1Bound5.coherentQuotientForm_normalized_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:22:53.041312+00:00
-- url     : https://prove2.me/submissions/d55d429f-6966-4a6b-9182-cb4524c763aa

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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Theorems.Thm_D1Bound5_coherent_half_binomial_exact
import Theorems.Thm_D1Bound5_coherent_interpolation_normalization

section
open Finset

namespace D1Bound5



/-- The normalized exact identity for the actual manuscript form,
including the precise coherent branch choices and all quotient weights. -/
theorem _root_.solution
    {m : ℕ} (a : Fin m → ℂ) (hm : 2 ≤ m)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (Delta p q eta : ℂ) (hDelta : Delta ≠ 0) (heta : eta ≠ 0)
    (hp : ∀ i, ‖p⁻¹ * (a i)⁻¹‖ < 1)
    (hq : ∀ i, ‖q⁻¹ * (a i)⁻¹‖ < 1) :
    coherentQuotientForm a Delta p q eta / (Delta * eta) =
      1 - ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)) +
        ((-1 : ℂ) ^ (m - 1) * (∏ i, a i)⁻¹) * coherentRemainder a p q := by
  let g : Fin m → ℂ := fun i =>
    ((1 + p⁻¹ * (a i)⁻¹) ^ (1 / 2 : ℂ)) *
      ((1 + q⁻¹ * (a i)⁻¹) ^ (1 / 2 : ℂ))
  have hs : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hnorm : coherentQuotientForm a Delta p q eta / (Delta * eta) =
      (∑ i, ((a i) ^ (m - 1) /
        (∏ j ∈ Finset.univ.erase i, (a i - a j))) * g i) -
        ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)) := by
    simpa only [coherentQuotientForm, coherentTerminalRoot, coherentAnchorRoot,
      Finset.card_univ, Fintype.card_fin, g, mul_assoc] using
      coherent_interpolation_normalization Finset.univ a g
        ((1 + p⁻¹ * q⁻¹) ^ (1 / 2 : ℂ)) Delta eta
        (by simpa using hm) hDelta heta
  have h := coherent_half_binomial_exact Finset.univ a hs
    (fun i _ => ha i) hinj.injOn p⁻¹ q⁻¹ (fun i _ => hp i) (fun i _ => hq i)
  have hsum : (∑ i, ((a i) ^ (m - 1) /
        (∏ j ∈ Finset.univ.erase i, (a i - a j))) * g i) =
      1 + ((-1 : ℂ) ^ (m - 1) * (∏ i, a i)⁻¹) * coherentRemainder a p q := by
    simpa only [Finset.card_univ, Fintype.card_fin, coherentRemainder, g] using h.2
  rw [hnorm, hsum]
  ring





end D1Bound5
end
