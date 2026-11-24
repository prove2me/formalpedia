-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_prod_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:58:46.69984+00:00
-- url     : https://prove2.me/submissions/1818c437-9baf-4be0-bda0-009c623ec784

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
open Classical
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (m : Fin r × Fin n →₀ ℕ) :
    (∏ v, (cwPt (R := R) v) ^ m v) = if LowerTri m then monomial (cwStrict m) 1 else 0 := by
  classical
  split_ifs with h
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    apply Finset.prod_congr rfl
    rintro ⟨a, s⟩ _
    rcases lt_trichotomy a.val s.val with c | c | c
    · have h0 := h a s c
      simp [cwStrict, h0, not_lt.mpr (le_of_lt c)]
    · simp [cwPt, idFrame, c, cwStrict]
    · simp [cwPt, idFrame, c, ne_of_gt c, cwStrict]
  · unfold LowerTri at h
    push Not at h
    obtain ⟨a, s, c, hne⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ (a, s))
    have h0 : cwPt (R := R) (a, s) = 0 := by simp [cwPt, idFrame, ne_of_lt c, not_lt.mpr (le_of_lt c)]
    rw [h0, zero_pow hne]
end Formalism.L2.G.Model.TS
