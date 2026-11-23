-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.lowOp_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:33.28937+00:00
-- url     : https://prove2.me/submissions/87a7ef44-9d88-408f-a8ea-c9eaf2c2bba7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_deg_ZV
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators
namespace Formalism.InvariantFactorPaths.G7.StarEntryOperators
theorem _root_.solution {K : Type} [Field K] (hM : MinorProdDegree) {ν r0 r1 C : ℕ} [NeZero ν]
    (l : Fin C → ℕ) (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K)
    (I : ∀ c, Fin (l c) → Fin r1) (n : ZV ν r0 r1 →₀ ℕ) (hn : n ∈ (lowOp l sf T I).support) :
    (∀ s, ∑ x : Fin r0 × Fin r1, n (s, x) = lsN l sf s) ∧ n.degree = ∑ s, lsN l sf s := by
  have hs := hM K (ZMod (2 * ν)) r0 r1 C l sf T I n hn
  refine ⟨hs, ?_⟩
  rw [deg_ZV]
  exact Finset.sum_congr rfl fun s _ => hs s
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
