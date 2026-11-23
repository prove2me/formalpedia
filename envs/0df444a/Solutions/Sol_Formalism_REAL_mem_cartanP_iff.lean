-- Prove2me | solution 1 for Formalism.REAL.mem_cartanP_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:06.793245+00:00
-- url     : https://prove2.me/submissions/6278f41b-8eae-45dc-81ec-cd281bf73168

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_anti_iff
import Theorems.Thm_Formalism_REAL_f1alg_inG_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inP ε X ↔ Xᴴ = X ∧ X * Jm ε = -(Jm ε * X) := by
  unfold inP
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩
end Formalism.REAL
