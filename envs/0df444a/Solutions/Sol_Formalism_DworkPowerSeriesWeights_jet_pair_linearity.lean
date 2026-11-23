-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jet_pair_linearity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:22.018699+00:00
-- url     : https://prove2.me/submissions/e172b9d5-6f6a-4bdf-85f2-a864376b16a0

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_poly
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_monomial_right
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : JetPairLin.{u} := by
  classical
  intro K _ ι ι' _ _ A P F
  set a : ι' → MvPowerSeries ι K :=
    fun j => ∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i with ha
  have ha0 : ∀ j, MvPowerSeries.constantCoeff (a j) = 0 := fun j => by simp [ha]
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hcoe : ∀ j, a j = ((linP A j : MvPolynomial ι K) : MvPowerSeries ι K) := fun j => by
    rw [ha, linP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    simp
  have hmon : ∀ μ : ι' →₀ ℕ, (μ.prod fun s e => a s ^ e) =
      ((MvPolynomial.aeval (linP A) (MvPolynomial.monomial μ (1 : K)) : MvPolynomial ι K) :
        MvPowerSeries ι K) := fun μ => by
    rw [MvPolynomial.aeval_monomial, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_mul,
      Finsupp.prod, Finsupp.prod, map_prod]
    simp [hcoe]
  change jetPair P (MvPowerSeries.subst a F) = jetPair (MvPolynomial.aeval (linP' A) P) F
  set P' := MvPolynomial.aeval (linP' A) P with hP'
  have hfin := fun κ => MvPowerSeries.coeff_subst_finite hs F κ
  set T : Finset (ι' →₀ ℕ) := (P.support.biUnion fun κ => (hfin κ).toFinset) ∪ P'.support with hT
  rw [jetPair_eq_sum P' F T Finset.subset_union_right]
  have h1 : ∀ κ ∈ P.support, MvPowerSeries.coeff κ (MvPowerSeries.subst a F) =
      ∑ μ ∈ T, MvPowerSeries.coeff μ F * MvPowerSeries.coeff κ (μ.prod fun s e => a s ^ e) := by
    intro κ hκ
    rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset]
    · rfl
    · intro μ hμ
      rw [hT, Finset.coe_union]
      left
      rw [Finset.coe_biUnion]
      exact Set.mem_biUnion hκ (by simpa using hμ)
  unfold jetPair
  rw [Finset.sum_congr rfl fun κ hκ => by rw [h1 κ hκ, Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h2 := jetPair_poly A P (MvPolynomial.monomial μ (1 : K))
  rw [jetPair_monomial_right, ← hmon] at h2
  rw [← hP'] at h2
  rw [← h2]
  unfold jetPair
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun κ _ => ?_
  ring
end Formalism.DworkPowerSeriesWeights
