-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.smat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:38.111122+00:00
-- url     : https://prove2.me/submissions/41291d76-c27b-49c9-94a7-e33e810357cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
import Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_smat_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.UkEmb
variable {n k : ℕ}
variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)
namespace Formalism.L2.SG.Pf.UkEmb
theorem _root_.solution (hJ2 : J * J = 1) (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1)
    (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0) :
    (J * (smat J wf G)ᴴ * J) * smat J wf G = 1 := by
  have h := smat_unitary J wf hon hJh G hG
  calc (J * (smat J wf G)ᴴ * J) * smat J wf G
      = J * ((smat J wf G)ᴴ * J * smat J wf G) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hJ2]
end Formalism.L2.SG.Pf.UkEmb
