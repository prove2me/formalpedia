-- Prove2me | solution 1 for Formalism.REAL.f1alg_inK_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:05.436002+00:00
-- url     : https://prove2.me/submissions/0a83750f-edae-42e0-91f0-00903f8fb449

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_comm_iff
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
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by
  unfold inK
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩
end Formalism.REAL
