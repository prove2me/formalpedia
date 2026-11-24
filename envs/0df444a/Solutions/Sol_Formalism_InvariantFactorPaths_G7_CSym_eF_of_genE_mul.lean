-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.eF_of_genE_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:44:42.363826+00:00
-- url     : https://prove2.me/submissions/57e925a3-9ee9-436f-ab3f-bc0fdb67eab4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_coeff_genE

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
open Formalism.InvariantFactorPaths.G7.CSym
variable {K σ : Type} [CommRing K] [Fintype σ]
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution {τ ρ : Type} [Fintype τ] [Fintype ρ] (z : σ → K) (x : τ → K) (y : ρ → K)
    (h : genE z = genE x * genE y) (n : ℕ) :
    eF z n = ∑ a ∈ range (n + 1), eF x a * eF y (n - a) := by
  rw [← coeff_genE, h, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_genE]
end Formalism.InvariantFactorPaths.G7.CSym
