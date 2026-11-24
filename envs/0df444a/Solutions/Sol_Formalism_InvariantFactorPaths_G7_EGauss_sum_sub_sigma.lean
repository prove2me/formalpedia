-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.sum_sub_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:44.73764+00:00
-- url     : https://prove2.me/submissions/c90a407f-e800-4082-941e-6995f085923a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss

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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGauss
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.EGauss
theorem _root_.solution {S : Type} [Fintype S] [DecidableEq S] (colN : S → ℕ)
    (P : (Σ s, Fin (colN s)) → Prop) [DecidablePred P] (f : (Σ s, Fin (colN s)) → ℕ) (s : S) :
    ∑ x : {x // P x}, (if x.1.1 = s then f x.1 else 0) =
      ∑ c : Fin (colN s), if P ⟨s, c⟩ then f ⟨s, c⟩ else 0 := by
  rw [← Finset.sum_subtype (univ.filter P) (by simp) (fun x => if x.1 = s then f x else 0),
    Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single s]
  · simp
  · intro s' _ h
    simp [h]
  · simp
end Formalism.InvariantFactorPaths.G7.EGauss
