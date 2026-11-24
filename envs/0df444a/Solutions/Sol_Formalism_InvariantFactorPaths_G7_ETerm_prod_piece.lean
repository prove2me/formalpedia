-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.prod_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:52.714135+00:00
-- url     : https://prove2.me/submissions/9bf092b8-cfa0-427f-9a06-1e39a0f92e55

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_prod_monomial
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_C_mul_monomial_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right


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
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K Tp Lw Φ κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
  [Fintype Φ] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ)
    (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ)
    (U : MvPowerSeries (Tp ⊕ Lw) K) :
    (∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U =
      (∏ x, lowLin (b x) ^ k (Sum.inr (Sum.inl x))) *
        (MvPowerSeries.monomial (dTot dA dB k) (cTot p aA aB k) *
          (Z ^ k (Sum.inr (Sum.inr 0)) * (Y ^ k (Sum.inr (Sum.inr 1)) * U))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_two]
  simp only [piece, Sum.elim_inl, Sum.elim_inr, if_true, one_ne_zero, if_false]
  have hA : ∏ φ, (MvPowerSeries.C (aA φ) * topMonoS (Lw := Lw) (dA φ)) ^ k (Sum.inl φ) =
      MvPowerSeries.monomial (∑ φ, k (Sum.inl φ) • (dA φ).mapDomain Sum.inl)
        (∏ φ, aA φ ^ k (Sum.inl φ)) := by
    rw [← prod_monomial]
    refine Finset.prod_congr rfl fun φ _ => ?_
    unfold topMonoS
    rw [C_mul_monomial_one, MvPowerSeries.monomial_pow]
  have hB : ∏ x, (MvPowerSeries.C (aB x) * topMonoS (Lw := Lw) (dB x) * lowLin (b x)) ^
        k (Sum.inr (Sum.inl x)) =
      MvPowerSeries.monomial (∑ x, k (Sum.inr (Sum.inl x)) • (dB x).mapDomain Sum.inl)
        (∏ x, aB x ^ k (Sum.inr (Sum.inl x))) * ∏ x, lowLin (b x) ^ k (Sum.inr (Sum.inl x)) := by
    rw [← prod_monomial, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    unfold topMonoS
    rw [C_mul_monomial_one, mul_pow, MvPowerSeries.monomial_pow]
  have hC : MvPowerSeries.monomial (dTot (Lw := Lw) dA dB k) (cTot p aA aB k) =
      MvPowerSeries.monomial (∑ φ, k (Sum.inl φ) • (dA φ).mapDomain Sum.inl)
        (∏ φ, aA φ ^ k (Sum.inl φ)) *
      MvPowerSeries.monomial (∑ x, k (Sum.inr (Sum.inl x)) • (dB x).mapDomain Sum.inl)
        (∏ x, aB x ^ k (Sum.inr (Sum.inl x))) *
      MvPowerSeries.C ((p : K)) ^ k (Sum.inr (Sum.inr 1)) := by
    rw [← map_pow, ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.monomial_mul_monomial, add_zero]
    rfl
  rw [hA, hB, hC, mul_pow]
  ring
end Formalism.InvariantFactorPaths.G7.ETerm
