-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:41:12.373795+00:00
-- url     : https://prove2.me/submissions/e44319f6-0542-42b1-87c3-e9077b6fbaf4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_continuous_pderiv
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
import Theorems.Thm_Formalism_FG_InjVAux_main


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution {R σ τ : Type} [CommRing R] [Fintype σ] {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (e : τ) (H : MvPowerSeries σ R) :
    pderiv R e (subst a H) = ∑ i, subst a (pderiv R i H) * pderiv R e (a i) := by
  classical
  let : UniformSpace R := ⊥
  have : DiscreteUniformity R := ⟨rfl⟩
  let := WithPiTopology.instTopologicalSpace (σ := τ) (R := R)
  let := WithPiTopology.instTopologicalSpace (σ := σ) (R := R)
  have := WithPiTopology.instIsTopologicalSemiring τ R
  have := WithPiTopology.instT2Space (σ := τ) (R := R)
  have hc1 : Continuous fun H : MvPowerSeries σ R => pderiv R e (subst a H) :=
    (continuous_pderiv e).comp (continuous_subst ha)
  have hc2 : Continuous fun H : MvPowerSeries σ R =>
      ∑ i, subst a (pderiv R i H) * pderiv R e (a i) :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_subst ha).comp (continuous_pderiv i)).mul continuous_const
  have main : ∀ P : MvPolynomial σ R, pderiv R e (subst a (P : MvPowerSeries σ R)) =
      ∑ i, subst a (pderiv R i (P : MvPowerSeries σ R)) * pderiv R e (a i) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C r =>
      have h0 : subst a (0 : MvPowerSeries σ R) = 0 := by
        rw [← coe_substAlgHom ha, map_zero]
      simp only [MvPolynomial.coe_C, subst_C, pderiv_C, h0, zero_mul, Finset.sum_const_zero]
    | add p q hp hq =>
      simp only [MvPolynomial.coe_add, subst_add ha, map_add, add_mul, Finset.sum_add_distrib]
      rw [hp, hq]
    | mul_X p j hp =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, subst_X ha,
        Derivation.leibniz, smul_eq_mul, subst_add ha, add_mul, Finset.sum_add_distrib]
      rw [hp, Finset.mul_sum]
      congr 1
      · rw [Finset.sum_eq_single j]
        · rw [pderiv_X_self, ← coe_substAlgHom ha, map_one, mul_one]
        · intro i _ hij
          rw [pderiv_X_of_ne hij.symm, ← coe_substAlgHom ha, map_zero, mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ j) h
      · exact Finset.sum_congr rfl fun i _ => by ring
  have key := WithPiTopology.denseRange_toMvPowerSeries (σ := σ) (R := R).equalizer hc1 hc2
    (funext main)
  exact congrFun key H
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
