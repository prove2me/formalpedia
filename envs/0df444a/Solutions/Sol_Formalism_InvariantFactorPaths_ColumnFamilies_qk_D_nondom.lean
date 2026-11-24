-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_D_nondom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:15.256267+00:00
-- url     : https://prove2.me/submissions/5c4e2180-32dc-4490-8110-4d2885a0adda

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_D_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_antitone_of_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (s : Finset (Fin n))
    (h : ¬ Dominant (qk_add mu s)) : qk_D (qk_v (qk_add mu s)) = 0 := by
  have h1 : ∃ a : Fin n, ∃ ha : a.1 + 1 < n, qk_add mu s a < qk_add mu s ⟨a.1 + 1, ha⟩ := by
    by_contra hc
    push Not at hc
    exact h (qk_antitone_of_step hc)
  obtain ⟨a, ha, hlt⟩ := h1
  have hle : mu ⟨a.1 + 1, ha⟩ ≤ mu a := hmu (by rw [Fin.le_def]; simp)
  have h2 : qk_add mu s ⟨a.1 + 1, ha⟩ = qk_add mu s a + 1 := by
    unfold qk_add at hlt ⊢
    split_ifs at hlt ⊢ <;> omega
  refine qk_D_zero (i := a) (j := ⟨a.1 + 1, ha⟩) (by rw [Fin.lt_def]; simp) ?_
  unfold qk_v
  rw [h2]
  push_cast
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
