-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.prime_order_element
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:22.283677+00:00
-- url     : https://prove2.me/submissions/240b1c9f-bc58-4fb8-a49c-699fbf683656

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : RationalMatrixPrimeOrderBound := by
  intro n p hp A hA h1
  classical
  haveI := Fact.mk hp
  have hint : IsIntegral ℚ A := Algebra.IsIntegral.isIntegral A
  have hm0 : minpoly ℚ A ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly ℚ A ∣ Polynomial.cyclotomic p ℚ * (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_prime_mul_X_sub_one ℚ p]
    apply minpoly.dvd
    simp [hA]
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) := Polynomial.cyclotomic.irreducible_rat hp.pos

  have hcd : Polynomial.cyclotomic p ℚ ∣ minpoly ℚ A := by
    by_contra hnd
    have hcop : IsCoprime (Polynomial.cyclotomic p ℚ) (minpoly ℚ A) := hirr.coprime_iff_not_dvd.2 hnd
    have hX : minpoly ℚ A ∣ Polynomial.X - 1 := hcop.symm.dvd_of_dvd_mul_left hdvd
    apply h1
    have h0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hX (minpoly.aeval ℚ A)
    simpa [sub_eq_zero] using h0
  have hle1 := Polynomial.natDegree_le_of_dvd hcd hm0
  have hle2 : (minpoly ℚ A).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A) (Matrix.charpoly_monic A).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp] at hle1
  omega
end Formalism.HermitianLattices.RamifiedHeckeModels
