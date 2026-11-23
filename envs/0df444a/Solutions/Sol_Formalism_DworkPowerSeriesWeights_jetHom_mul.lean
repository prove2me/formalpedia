-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetHom_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:24.749275+00:00
-- url     : https://prove2.me/submissions/f12334de-4651-474f-a818-9e4a93c306aa

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
theorem _root_.solution {n1 n2 : σ →₀ ℕ} {f g : MvPowerSeries ι K} (hf : jetHom lt n1 f)
    (hg : jetHom lt n2 g) : jetHom lt (n1 + n2) (f * g) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : MvPowerSeries.coeff p.1 f ≠ 0 := left_ne_zero_of_mul hne
  have h2 : MvPowerSeries.coeff p.2 g ≠ 0 := right_ne_zero_of_mul hne
  rw [← hp, Finsupp.mapDomain_add, hf _ h1, hg _ h2]
end Formalism.DworkPowerSeriesWeights
