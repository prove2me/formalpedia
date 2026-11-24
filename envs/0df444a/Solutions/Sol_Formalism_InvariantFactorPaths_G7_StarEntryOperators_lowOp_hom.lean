-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.lowOp_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:38.852171+00:00
-- url     : https://prove2.me/submissions/b8675cbf-c354-48be-b72a-f39e67b77e02

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_StarEntryOperators_lowOp_deg

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
    (I : ∀ c, Fin (l c) → Fin r1) : (lowOp l sf T I).IsHomogeneous (∑ s, lsN l sf s) := by
  intro n hn
  have h := (lowOp_deg hM l sf T I n (MvPolynomial.mem_support_iff.mpr hn)).2
  rw [← h, Finsupp.degree_eq_weight_one]
  rfl
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
