-- Prove2me | solution 1 for Formalism.L2.Th1.A.More.iterate_D_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:51:07.585654+00:00
-- url     : https://prove2.me/submissions/dabee8b8-f11b-4199-9587-b942919c58b9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_More_D_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
open Formalism.L2.Th1.A.More
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)
namespace Formalism.L2.Th1.A.More
theorem _root_.solution (hw : ∀ n, coeff n (fw W) ∈ S) (k : ℕ) (f : K⟦X⟧)
    (hf : ∀ n, coeff n f ∈ S) (n : ℕ) : coeff n ((D W)^[k] f) ∈ S := by
  induction k generalizing f n with
  | zero => exact hf n
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact D_mem W S hw _ (fun m => ih f hf m) n
end Formalism.L2.Th1.A.More
