-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_zetaMul_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:46:27.31432+00:00
-- url     : https://prove2.me/submissions/f4a86943-567b-43e0-8e2f-a1f6825acf7b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_zetaMul_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation ComplexOrder
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    (a : ℕ) : zetaMul χ (p ^ a) = ∑ i ∈ range (a + 1), χ (p : ZMod M) ^ i := by
  rw [dhpr_zetaMul_eq_sum, Nat.divisors_prime_pow hp, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp [Nat.cast_pow, map_pow]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
