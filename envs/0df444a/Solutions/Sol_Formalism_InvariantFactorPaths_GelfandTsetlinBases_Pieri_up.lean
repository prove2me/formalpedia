-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:50.042197+00:00
-- url     : https://prove2.me/submissions/627e0876-0177-4690-8b68-7225bb690c1c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_stripsUp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_dGT_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_antitone_of_mem_gtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sum_sLe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_toggle_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_hockey

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
theorem _root_.solution (n : ℕ) : ∀ (μ : Fin n → ℤ) (b : ℕ), Antitone μ →
    ∑ ν ∈ stripsUp μ b, dGT n ν = dGT n μ * (n + b - 1).choose b := by
  induction n with
  | zero =>
    intro μ b _
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have e : stripsUp μ 0 = {μ} := by
        ext ν
        rw [mem_stripsUp, Finset.mem_singleton]
        constructor
        · intro _
          exact Subsingleton.elim _ _
        · rintro rfl
          unfold HStrip
          simp
      rw [e, Finset.sum_singleton]
      simp
    · have e : stripsUp μ b = ∅ := by
        ext ν
        rw [mem_stripsUp]
        simp [HStrip]
        omega
      rw [e, Finset.sum_empty, Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  | succ n ih =>
    intro μ b hμ
    simp only [dGT_succ]
    rw [toggle_sum μ b (dGT n)]
    have e : ∀ κ ∈ gtBox μ, ∑ l ∈ sLe κ b, dGT n l = dGT n κ * (n + b).choose b := by
      intro κ hκ
      rw [sum_sLe, ← hockey n b, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      exact ih κ c (antitone_of_mem_gtBox hμ hκ)
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, show n + 1 + b - 1 = n + b by omega]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
