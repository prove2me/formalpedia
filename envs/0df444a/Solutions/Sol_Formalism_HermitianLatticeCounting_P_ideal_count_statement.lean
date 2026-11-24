-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_count_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:59.992804+00:00
-- url     : https://prove2.me/submissions/46f6b345-f0f3-40f5-bd50-09245cc97950

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Theorems.Thm_Formalism_SLP_Final_omegaPow
import Theorems.Thm_Formalism_SLP_Final_submoduleIndexCountO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CardSubmodulesOfIndexLePow := by
  intro E _ _ M _ _ _ _ k j hj hk
  obtain ⟨hfin, hcard⟩ := Formalism.SLP.Final.submoduleIndexCountO E M j hj
  refine ⟨hfin, ?_⟩
  have hd : 1 ≤ finrank ℚ E := Module.finrank_pos
  have hom := Formalism.SLP.Final.omegaPow (finrank ℚ E) j hd hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  calc ((({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.ncard : ℕ)) : ℝ)
      ≤ ((finrank ℚ E ^ (Nat.primeFactorsList j).length *
          j ^ finrank (NumberField.RingOfIntegers E) M : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (finrank ℚ E : ℝ) ^ (Nat.primeFactorsList j).length *
          (j : ℝ) ^ finrank (NumberField.RingOfIntegers E) M := by push_cast; ring
    _ ≤ (j : ℝ) ^ Real.logb 2 (finrank ℚ E) * (j : ℝ) ^ (k : ℝ) := by
          gcongr
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hj1 (by exact_mod_cast hk)
    _ = (j : ℝ) ^ ((k : ℝ) + Real.logb 2 (finrank ℚ E)) := by
          rw [Real.rpow_add (by linarith)]; ring
end Formalism.HermitianLatticeCounting.P
