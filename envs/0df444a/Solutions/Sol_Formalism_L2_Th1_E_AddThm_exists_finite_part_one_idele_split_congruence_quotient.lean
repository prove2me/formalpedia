-- Prove2me | solution 1 for Formalism.L2.Th1.E.AddThm.exists_finite_part_one_idele_split_congruence_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:39.44889+00:00
-- url     : https://prove2.me/submissions/fdff3fb6-9edc-41ca-b892-68832f7d79db

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Theorems.Thm_Formalism_L2_Th1_E_AddThm_rat_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AddThm
open Formalism.L2.Th1
variable (L : PeriodPair)
namespace Formalism.L2.Th1.E.AddThm
theorem _root_.solution (s : ℂ) : ∃ u : ℂ, 2 * u ∉ L.lattice ∧ s + u ∉ L.lattice ∧ s - u ∉ L.lattice := by
  by_cases h : s + L.ω₁ / 3 ∈ L.lattice ∨ s - L.ω₁ / 3 ∈ L.lattice
  · refine ⟨L.ω₁ / 5, rat_notMem L (2 / 5) (by norm_num) _ (by push_cast; ring), ?_, ?_⟩
    · intro h5
      rcases h with h | h
      · exact rat_notMem L (2 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h h5)
      · exact rat_notMem L (8 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h5 h)
    · intro h5
      rcases h with h | h
      · exact rat_notMem L (8 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h h5)
      · exact rat_notMem L (2 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h5 h)
  · push Not at h
    exact ⟨L.ω₁ / 3, rat_notMem L (2 / 3) (by norm_num) _ (by push_cast; ring), h.1, h.2⟩
end Formalism.L2.Th1.E.AddThm
