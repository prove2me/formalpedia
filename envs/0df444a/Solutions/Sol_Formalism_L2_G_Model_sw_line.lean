-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:32.24988+00:00
-- url     : https://prove2.me/submissions/ba5518a4-a345-464f-978f-b6e6da2a586c

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_L2_G_Model_sw_kill
import Theorems.Thm_Formalism_L2_G_Model_sw_eval_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model
theorem _root_.solution (K : Type) [Field K] [Infinite K] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) K) (hG : G ∈ dualWeyl K r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν)) :
    G = eval (idPoint K r n) G • hw K hn ν := by
  obtain ⟨c, hc⟩ := hwLine K r n hn ν hν G hG (fun a b hab k hk => sw_kill K hn ν G hG hGh a b hab k hk)
  have h1 : eval (idPoint K r n) G = c := by
    rw [hc, smul_eq_C_mul, map_mul, eval_C, sw_eval_hw, mul_one]
  rw [h1]
  exact hc
end Formalism.L2.G.Model
