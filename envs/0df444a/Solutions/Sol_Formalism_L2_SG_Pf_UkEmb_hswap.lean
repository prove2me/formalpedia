-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.hswap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:13:09.005059+00:00
-- url     : https://prove2.me/submissions/1a7a294b-02ab-49f6-9eb3-5e6de5c07404

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
theorem _root_.solution (J : Matrix (Fin n) (Fin n) ℂ) (hJh : Jᴴ = J) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (J *ᵥ y) = star (star y ⬝ᵥ (J *ᵥ x)) := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => by
    rw [← Matrix.conjTranspose_apply, hJh]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end Formalism.L2.SG.Pf.UkEmb
