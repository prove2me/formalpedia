-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.gauss_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:47.213613+00:00
-- url     : https://prove2.me/submissions/a665f89e-84c9-4fc0-900c-ccad4cf360ac

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_of_card_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_beFam_succ
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_succ_succ
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_zero_right
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_zero_succ


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
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution (Q : ℕ) (hQ : (Q : K) ≠ 0) : ∀ g l : ℕ,
    ((Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) =
      (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l)) * eF (beFam (Q : K) g) l
  | g, 0 => by
    rw [Formalism.G0.QVandermondeP.gb_zero_right, eF_zero]; simp
  | 0, l + 1 => by
    rw [Formalism.G0.QVandermondeP.gb_zero_succ, eF_of_card_lt _ _ (by simp)]; simp
  | g + 1, l + 1 => by
    rw [Formalism.G0.QVandermondeP.gb_succ_succ, eF_beFam_succ _ hQ]
    push_cast
    rw [solution Q hQ g l, solution Q hQ g (l + 1)]
    push_cast
    generalize eF (beFam (Q : K) g) l = E0
    generalize eF (beFam (Q : K) g) (l + 1) = E1
    have h1 : (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l)) =
        (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) + 1 - ((l : ℤ) + 1))) * (Q : K) ^ (-(g : ℤ)) *
          (Q : K) ^ l := by
      rw [← zpow_natCast, ← zpow_add₀ hQ, ← zpow_add₀ hQ]
      congr 1
      ring
    have h2 : ((Q : K) ^ 2) ^ (l + 1) * (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) - ((l : ℤ) + 1))) =
        (Q : K) ^ (((l : ℤ) + 1) * ((g : ℤ) + 1 - ((l : ℤ) + 1))) * (Q : K) ^ (l + 1) := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast (Q : K) (l + 1), ← zpow_add₀ hQ,
        ← zpow_add₀ hQ]
      congr 1
      push_cast
      ring
    linear_combination E0 * h1 + E1 * h2
end Formalism.InvariantFactorPaths.G7.CSym
