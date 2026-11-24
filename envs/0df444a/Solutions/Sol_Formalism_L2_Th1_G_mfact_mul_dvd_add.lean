-- Prove2me | solution 1 for Formalism.L2.Th1.G.mfact_mul_dvd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:30.402903+00:00
-- url     : https://prove2.me/submissions/6f8123c1-0a9b-4e71-83e1-5be8f9ef43a4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key


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
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)
namespace Formalism.L2.Th1.G
theorem _root_.solution {ι : Type} (μ ν : ι →₀ ℕ) : mfact μ * mfact ν ∣ mfact (μ + ν) := by
  classical
  have key : ∀ κ : ι →₀ ℕ, κ.support ⊆ μ.support ∪ ν.support →
      mfact κ = ∏ i ∈ μ.support ∪ ν.support, (κ i).factorial := by
    intro κ hκ
    exact Finsupp.prod_of_support_subset κ hκ (fun _ k => k.factorial) (fun _ _ => rfl)
  rw [key μ Finset.subset_union_left, key ν Finset.subset_union_right,
    key (μ + ν) Finsupp.support_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => by
    rw [Finsupp.add_apply]
    exact Nat.factorial_mul_factorial_dvd_factorial_add _ _)
end Formalism.L2.Th1.G
