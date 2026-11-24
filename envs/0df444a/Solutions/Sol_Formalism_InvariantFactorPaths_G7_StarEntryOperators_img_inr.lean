-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.img_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:56.835334+00:00
-- url     : https://prove2.me/submissions/cb04e65e-1e9e-442d-8416-517be2521831

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd

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
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.StarEntryOperators
theorem _root_.solution [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K)
    (y : ZV ν r0 r1) :
    (∑ x, MvPolynomial.C (Amat TT ξ (Sum.inr y) x) * MvPolynomial.X x :
      MvPolynomial (ZV ν r0 r1) K) = MvPolynomial.X y := by
  rw [Finset.sum_eq_single y]
  · simp [Amat]
  · intro x _ hx
    simp [Amat, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
