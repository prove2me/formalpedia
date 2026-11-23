-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spCore
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:06.181514+00:00
-- url     : https://prove2.me/submissions/b7f8fbb9-dc0d-495e-ad2f-89c32c92c783

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spLdeg_single
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spProd_ldeg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spPair

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
variable (lt : ι → σ) (N : σ → ι → R)
variable {lt N} (hN : ∀ s k, N s k ≠ 0 → lt k = s)
include hN
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (f : MvPowerSeries σ R) (i j : ι) (a b : ℕ) (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
      (MvPowerSeries.subst (fun s => ∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) f) =
      MvPowerSeries.coeff (Finsupp.single (lt i) a + Finsupp.single (lt j) b) f *
        (N (lt i) i ^ a * N (lt j) j ^ b) := by
  have hsub : MvPowerSeries.HasSubst
      (fun s => ∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k : σ → MvPowerSeries ι R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  rw [MvPowerSeries.coeff_subst hsub,
    finsum_eq_single _ (Finsupp.single (lt i) a + Finsupp.single (lt j) b)]
  · rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by rw [pow_zero]), Finsupp.prod_single_index (by rw [pow_zero]),
      smul_eq_mul, spPair hN i j a b hij]
  · intro dd hdd
    have hz : MvPowerSeries.coeff (Finsupp.single i a + Finsupp.single j b)
        (dd.prod fun s e => (∑ k, MvPowerSeries.C (N s k) * MvPowerSeries.X k) ^ e) = 0 := by
      by_contra hne
      apply hdd
      have hl := spProd_ldeg hN dd.support dd _ hne
      ext t
      have ht := hl t
      rw [spLdeg_add, spLdeg_single, spLdeg_single] at ht
      have hdt : (if t ∈ dd.support then dd t else 0) = dd t := by
        split_ifs with hm
        · rfl
        · exact (Finsupp.notMem_support_iff.mp hm).symm
      rw [hdt] at ht
      rw [← ht, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    rw [hz, smul_zero]
end Formalism.DworkPowerSeriesWeights
