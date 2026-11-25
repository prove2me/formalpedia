-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.coeff_tensor4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:37:56.247563+00:00
-- url     : https://prove2.me/submissions/dd4b2574-17ac-4651-b252-e5b534255bcd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_blk_apply
import Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_tensor4_eq_rename

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations
open Formalism.L2.Th1.E.GeneratorMatrix
variable {K : Type} [Field K] {n : Type}
namespace Formalism.L2.Th1.E.GeneratorMatrix
theorem _root_.solution (f : MvPowerSeries n K) (ν : n →₀ ℕ) :
    MvPowerSeries.coeff (∑ a, Finsupp.embDomain (blk n a) ν) (tensor4 f) =
      MvPowerSeries.coeff ν f ^ 4 := by
  classical
  rw [tensor4_eq_rename, MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun a => Finsupp.embDomain (blk n a) ν)]
  · simp
  · intro L hL hne
    by_contra h0
    apply hne
    rw [Finset.mem_finsuppAntidiag] at hL
    have hr : ∀ a, ∃ μ : n →₀ ℕ, L a = Finsupp.embDomain (blk n a) μ := by
      intro a
      by_contra hc
      apply h0
      refine Finset.prod_eq_zero (Finset.mem_univ a) (MvPowerSeries.coeff_rename_eq_zero _ _ ?_)
      rintro ⟨μ, hμ⟩
      exact hc ⟨μ, by rw [Finsupp.embDomain_eq_mapDomain, hμ]⟩
    choose μ hμ using hr
    have hμν : ∀ b, μ b = ν := by
      intro b
      ext i
      have := DFunLike.congr_fun hL.1 (b, i)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, hμ, blk_apply, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      exact this
    ext1 a
    rw [hμ, hμν]
    rfl
  · intro h
    exact absurd (by simp [Finset.mem_finsuppAntidiag]) h
end Formalism.L2.Th1.E.GeneratorMatrix
