-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:20.991023+00:00
-- url     : https://prove2.me/submissions/65b4ed9d-fe80-4a9d-baef-dd20f79da8c3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary

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
namespace Formalism.L2.SG.Pf.UkEmb
theorem _root_.solution (wf : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin k) :
    ((Wm wf)ᴴ * M * Wm wf) a b = star (wf a) ⬝ᵥ (M *ᵥ wf b) := by
  first
  | (rw [Matrix.mul_assoc]; rfl)
  | (simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Wm, Matrix.of_apply, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
     rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
end Formalism.L2.SG.Pf.UkEmb
