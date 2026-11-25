-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_prod_inBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:51:19.590012+00:00
-- url     : https://prove2.me/submissions/0d7bfb4e-fc7e-4aa5-90cd-9212ee48efb2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_coeff_inBlock_embDomain
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_exists_of_coeff_inBlock_ne_zero
import Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_rep_apply

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
open Formalism.L2.Th1.G.HurwitzJetIntegrality
namespace Formalism.L2.Th1.G.HurwitzJetIntegrality
theorem _root_.solution {K : Type} [Field K] {ι B : Type} [Fintype B]
    (f : MvPowerSeries ι K) (κ : ι →₀ ℕ) :
    MvPowerSeries.coeff (rep B fun _ => κ) (∏ k : B, inBlock k f) =
      (MvPowerSeries.coeff κ f) ^ Fintype.card B := by
  classical
  rw [MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (blockEmb B ι k) κ)]
  · rw [Finset.prod_congr rfl (fun k _ => show MvPowerSeries.coeff
        ((Finsupp.equivFunOnFinite.symm fun k => Finsupp.embDomain (blockEmb B ι k) κ) k) (inBlock k f) =
        MvPowerSeries.coeff κ f from coeff_inBlock_embDomain k f κ)]
    rw [Finset.prod_const, Finset.card_univ]
  · intro l hl hne
    by_contra hprod
    apply hne
    have hex : ∀ k, ∃ m : ι →₀ ℕ, l k = Finsupp.embDomain (blockEmb B ι k) m := fun k =>
      exists_of_coeff_inBlock_ne_zero k f (l k) (fun h0 => hprod (Finset.prod_eq_zero (Finset.mem_univ k) h0))
    choose m hm using hex
    rw [Finset.mem_finsuppAntidiag] at hl
    ext k : 1
    show l k = Finsupp.embDomain (blockEmb B ι k) κ
    rw [hm k]
    congr 1
    ext i
    have h1 := congrArg (fun x : B × ι →₀ ℕ => x (k, i)) hl.1
    simp only [Finsupp.finset_sum_apply, rep_apply, hm] at h1
    rw [Finset.sum_eq_single k] at h1
    · rw [← h1]
      symm
      first
        | exact Finsupp.embDomain_apply_self (blockEmb B ι k) (m k) i
        | exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := m k) (a := i)
        | simp [Finsupp.embDomain_apply, blockEmb]
    · intro k' _ hk'
      rw [Finsupp.embDomain_notin_range]
      rintro ⟨j, hj⟩
      exact hk' (congrArg Prod.fst hj)
    · intro h
      exact absurd (Finset.mem_univ k) h
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
    ext ⟨k, i⟩
    rw [Finsupp.finset_sum_apply, rep_apply, Finset.sum_eq_single k]
    · show (Finsupp.embDomain (blockEmb B ι k) κ) (k, i) = κ i
      first
        | exact Finsupp.embDomain_apply_self (blockEmb B ι k) κ i
        | exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := κ) (a := i)
        | simp [Finsupp.embDomain_apply, blockEmb]
    · intro k' _ hk'
      show (Finsupp.embDomain (blockEmb B ι k') κ) (k, i) = 0
      rw [Finsupp.embDomain_notin_range]
      rintro ⟨j, hj⟩
      exact hk' (congrArg Prod.fst hj)
    · intro h
      exact absurd (Finset.mem_univ k) h
end Formalism.L2.Th1.G.HurwitzJetIntegrality
