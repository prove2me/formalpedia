-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_poly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:59.133278+00:00
-- url     : https://prove2.me/submissions/9236213c-3e8f-4d9d-9d89-ba91402780f8

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_add_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_mul_X
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_pderiv_aeval_linP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_aeval_linP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
section JetPair
variable {K : Type u} [Field K] {ι : Type}
end JetPair
section Chain
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']
private theorem mvPowerSeries_pderiv_coe_eq_coe_pderiv {L : Type u} [Field L] {σ : Type} (i : σ)
    (G : MvPolynomial σ L) :
    MvPowerSeries.pderiv L i (G : MvPowerSeries σ L) =
      ((MvPolynomial.pderiv i G : MvPolynomial σ L) : MvPowerSeries σ L) := by
  ext n
  rw [MvPowerSeries.coeff_pderiv, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_pderiv]
end Chain
section Frames
end Frames
end Formalism.DworkPowerSeriesWeights
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (A : ι → ι' → K) (P : MvPolynomial ι K) :
    ∀ G : MvPolynomial ι' K,
      jetPair P ((MvPolynomial.aeval (linP A) G : MvPolynomial ι K) : MvPowerSeries ι K) =
        jetPair (MvPolynomial.aeval (linP' A) P) (G : MvPowerSeries ι' K) := by
  classical
  induction P using MvPolynomial.induction_on
  · rename_i c
    intro G
    rw [jetPair_C_left, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, jetPair_C_left]
    congr 1
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_coe]
    have h := constantCoeff_aeval_linP A G
    first
    | exact h
    | simpa [MvPolynomial.constantCoeff_eq] using h
  · rename_i P Q hP hQ
    intro G
    rw [jetPair_add_left, hP, hQ, map_add, jetPair_add_left]
  · rename_i P i hP
    intro G
    have hsum : ∀ (f : ι' → MvPolynomial ι K),
        ((∑ j, f j : MvPolynomial ι K) : MvPowerSeries ι K) = ∑ j, (f j : MvPowerSeries ι K) := by
      intro f
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
    rw [jetPair_mul_X, mvPowerSeries_pderiv_coe_eq_coe_pderiv, pderiv_aeval_linP, hsum, jetPair_sum_right]
    rw [map_mul, MvPolynomial.aeval_X]
    rw [linP']
    rw [Finset.mul_sum, jetPair_sum_left]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_C, jetPair_C_mul_right, hP,
      show MvPolynomial.aeval (linP' A) P * (MvPolynomial.C (A i j) * MvPolynomial.X j) =
        MvPolynomial.C (A i j) * (MvPolynomial.aeval (linP' A) P * MvPolynomial.X j) by ring,
      jetPair_C_mul_left, jetPair_mul_X, mvPowerSeries_pderiv_coe_eq_coe_pderiv]
end Formalism.DworkPowerSeriesWeights
