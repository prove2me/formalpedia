-- Prove2me | solution 1 for Formalism.ResultantValuation.ParabolicCounting.mem_stabilizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:26.347835+00:00
-- url     : https://prove2.me/submissions/673fb47c-1e70-46b8-a7e9-65bf1d1c0ee6

import Definitions.Def_Formalism_ResultantValuation_SubspaceCount
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
import Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_smul_def
import Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_finrank_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ResultantValuation
open Module
open Formalism.ResultantValuation.ParabolicCounting
variable (F : Type) [Field F] (r t : ℕ)
attribute [local instance] act
namespace Formalism.ResultantValuation.ParabolicCounting
theorem _root_.solution (g : GL (Fin (r + t)) F) :
    g ∈ MulAction.stabilizer (GL (Fin (r + t)) F) (firstBlock F r t) ↔
      g ∈ parabolicSet F r t := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h i j hi hj
    have hmem : (Pi.single j (1 : F) : Fin (r + t) → F) ∈ firstBlock F r t := by
      intro k hk
      have hkj : k ≠ j := by
        intro e
        subst e
        omega
      simp [hkj]
    have h2 : Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F) (Pi.single j 1) ∈
        firstBlock F r t := by
      rw [← h, smul_def]
      exact Submodule.mem_map_of_mem hmem
    have h3 := h2 i hi
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using h3
  · intro hg
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [smul_def]
      rintro _ ⟨v, hv, rfl⟩ i hi
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : (j : ℕ) < r
      · simp [hg i j hi hj]
      · simp [hv j (by omega)]
    · exact finrank_smul F r t g _
end Formalism.ResultantValuation.ParabolicCounting
