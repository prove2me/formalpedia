-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetHom_substProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:44.595292+00:00
-- url     : https://prove2.me/submissions/423177da-7524-40a0-9984-c52d5c030f39

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameCoeffMulLin
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetHom_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetHom_prod

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
variable {K : Type u} [NormedField K] {ι σ : Type*} (lt : ι → σ)
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (a : σ → MvPowerSeries ι K)
    (ha : ∀ t, jetHom lt (Finsupp.single t 1) (a t)) (n : σ →₀ ℕ) :
    jetHom lt n (n.prod fun s e => a s ^ e) := by
  classical
  have h := jetHom_prod lt n.support (fun s => n s • Finsupp.single s 1) (fun s => a s ^ n s)
    fun s _ => jetHom_pow lt (ha s) (n s)
  have hd : ∑ s ∈ n.support, n s • Finsupp.single s 1 = n := by
    simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.sum_single n
  rw [hd] at h
  simpa [Finsupp.prod] using h
end Formalism.DworkPowerSeriesWeights
