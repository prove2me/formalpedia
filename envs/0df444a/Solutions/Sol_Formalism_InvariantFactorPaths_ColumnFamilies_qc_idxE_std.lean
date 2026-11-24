-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_idxE_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:49.817273+00:00
-- url     : https://prove2.me/submissions/bffee09d-085e-4cf9-a32a-cc62eb4fe6ae

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colE_val
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_idxE_val
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_colE_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) : StdT I ↔ StdT (qc_idxE mu ε I) := by
  constructor
  · intro h c hc t
    have hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε) := by
      have := (qc_mem_sh mu ε (c.1 + 1)).2 hc
      rw [qc_colE_val]
      convert this using 1
      ring
    have h1 := h (qc_colE mu ε c) hc' t
    rw [qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc']
    exact h1
  · intro h c' hc' t
    obtain ⟨c, rfl⟩ := (qc_colE mu ε).surjective c'
    have hc : c.1 + 1 ∈ TCols mu := by
      apply (qc_mem_sh mu ε (c.1 + 1)).1
      rw [qc_colE_val] at hc'
      convert hc' using 1
      ring
    have h1 := h c hc t
    rw [qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc'] at h1
    exact h1
end Formalism.InvariantFactorPaths.ColumnFamilies
