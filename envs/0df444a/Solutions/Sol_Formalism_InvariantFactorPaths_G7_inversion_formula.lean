-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.inversion_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:51.658436+00:00
-- url     : https://prove2.me/submissions/8064c60e-c521-4daf-992f-8c0377081018

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_conv_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_sum_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_comp_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_hecke_convolution
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_iterate_statement

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
open CSym
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : Inversion := by
  intro K _ M _ _ Kk e Q t m J hI j hj r
  have hit := iterate_statement K M Kk e Q t m J hI j hj
  rw [CSym.sum_comp]
  simp_rw [LinearMap.smul_comp, hit, ← LinearMap.comp_smul, ← CSym.comp_sum]
  congr 1
  rw [conv_smul, Finset.sum_eq_single 0]
  · simp [hF, eF_zero, MvPolynomial.hsymm_zero]
  · intro n _ hn0
    rw [hecke_convolution K _ (FFam Q t m j) n (by omega), zero_smul]
  · intro h
    simp at h
end Formalism.InvariantFactorPaths.G7
