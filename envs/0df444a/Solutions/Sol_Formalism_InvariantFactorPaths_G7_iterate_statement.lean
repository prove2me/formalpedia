-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.iterate_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:19.59655+00:00
-- url     : https://prove2.me/submissions/de43160f-1bc9-4c16-8cd6-41068ed5c562

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_of_genE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_isEmpty
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_conv_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_sum_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_comp_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_genE_FFam_succ

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
theorem _root_.solution : Iterate := by
  intro K _ M _ _ Kk e Q t m J hI j
  induction j with
  | zero =>
    intro _ i
    simp only [Kc, LinearMap.comp_id, LinearMap.id_comp]
    rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [eF_isEmpty, if_neg hl, zero_smul])
      (by simp), eF_isEmpty, if_pos rfl, one_smul, Nat.sub_zero]
  | succ j ih =>
    intro hj i
    have ih' := ih (by omega)
    show (e (j + 1) i).comp ((Kk j).comp (Kc Kk j)) =
      ((Kk j).comp (Kc Kk j)).comp (∑ l ∈ range (i + 1), eF (FFam Q t m (j + 1)) l • e 0 (i - l))
    rw [← LinearMap.comp_assoc, hI j (by omega) i, LinearMap.comp_assoc, CSym.sum_comp]
    simp_rw [LinearMap.smul_comp, ih', ← LinearMap.comp_smul, ← CSym.comp_sum]
    rw [← LinearMap.comp_assoc]
    congr 1
    rw [conv_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eF_of_genE_mul _ _ _ (genE_FFam_succ Q t m j) n]
end Formalism.InvariantFactorPaths.G7
