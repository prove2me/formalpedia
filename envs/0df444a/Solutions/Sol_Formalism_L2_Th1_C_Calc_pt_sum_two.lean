-- Prove2me | solution 1 for Formalism.L2.Th1.C.Calc.pt_sum_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:39:01.942997+00:00
-- url     : https://prove2.me/submissions/fe615494-6f1d-4673-a5e7-bfb2599ef705

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ArithmeticFrobeniusAction
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourFoldOrthogonalSum
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FinsuppZmodOneEqSingle
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Theorems.Thm_Formalism_L2_Th1_C_Calc_pt_sum
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_LT_InvIntP_key


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Calc
open Pts Formalism.HermitianLattices.IntegralLatticeDensity
variable {K : Type} [Field K] [CharZero K] {O : Type} [CommRing O] [StarRing O]
variable {R : Subring K} {l linv : PowerSeries K} {τ : O →+* K}
namespace Formalism.L2.Th1.C.Calc
theorem _root_.solution (D : Data R l linv τ) {σ : Type} {n : Type} [Fintype n] (c c' : n → O)
    (t t' : n → MvPowerSeries σ K) (ht : ∀ j, IsPt R (t j)) (ht' : ∀ j, IsPt R (t' j)) :
    pt D (∑ j, (c j • toM D (t j) (ht j) + c' j • toM D (t' j) (ht' j))) =
      flin l linv (Sum.elim (fun j => τ (c j)) (fun j => τ (c' j))) (Sum.elim t t') := by
  have hs : ∀ k, IsPt R (Sum.elim t t' k) := by
    intro k
    cases k with
    | inl j => exact ht j
    | inr j => exact ht' j
  have key := pt_sum D (Sum.elim c c') (Sum.elim t t') hs
  have e1 : (fun k => τ (Sum.elim c c' k)) = Sum.elim (fun j => τ (c j)) (fun j => τ (c' j)) := by
    funext k
    cases k <;> rfl
  rw [e1] at key
  rw [← key, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  try rfl
end Formalism.L2.Th1.C.Calc
