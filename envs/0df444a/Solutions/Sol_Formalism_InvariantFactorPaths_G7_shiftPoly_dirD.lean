-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.shiftPoly_dirD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:39.006102+00:00
-- url     : https://prove2.me/submissions/99675bf4-7bc3-4623-be45-a9ae1449ce40

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_pderiv_shiftGen
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K ι κ : Type} [Field K] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution [Fintype ι] (b : κ → ι → K) (k : κ) (Q : MvPolynomial ι K) :
    shiftPoly b (dirD (b k) Q) = MvPolynomial.pderiv k (shiftPoly b Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [dirD, shiftPoly_C, shiftPoly_zero]
  | add p q hp hq =>
    have : dirD (b k) (p + q) = dirD (b k) p + dirD (b k) q := by
      simp only [dirD, map_add, mul_add, Finset.sum_add_distrib]
    rw [this, shiftPoly_add, shiftPoly_add, map_add, hp, hq]
  | mul_X p x hp =>
    have : dirD (b k) (p * MvPolynomial.X x) =
        dirD (b k) p * MvPolynomial.X x + p * MvPolynomial.C (b k x) := by
      simp only [dirD, MvPolynomial.pderiv_mul, mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · rw [Finset.sum_eq_single x]
        · rw [MvPolynomial.pderiv_X_self]
          ring
        · intro j _ hj
          rw [MvPolynomial.pderiv_X_of_ne hj.symm]
          simp
        · intro h
          exact absurd (Finset.mem_univ x) h
    rw [this, shiftPoly_add, shiftPoly_mul, shiftPoly_mul, shiftPoly_mul, hp, shiftPoly_X,
      shiftPoly_C, MvPolynomial.pderiv_mul, pderiv_shiftGen]
end Formalism.InvariantFactorPaths.G7
