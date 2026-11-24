-- Prove2me | solution 1 for FairSelling.exists_threequarter_MMS_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:15.576591+00:00
-- url     : https://prove2.me/submissions/041b2bda-0e76-4338-9a33-98b180c20e5c

import Mathlib
import Definitions.Def_RequestProject_PreliminaryPhase
import Definitions.Def_RequestProject_ThreeAgentTheorem
import Theorems.Thm_FairSelling_preliminary_stage_one
import Theorems.Thm_FairSelling_preliminary_stage_two
import Theorems.Thm_P2M_FairSelling_exists_threequarter_MMS_three_nobig__2b81d0860f2f


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  by_cases hexp : ∃ (i : Fin 3) (g : G), (3 / 4 : ℝ) * MMS 3 (v i) p ≤ p g
  · -- Stage 1 of the preliminary phase: some good is expensive.
    obtain ⟨i0, e, he⟩ := hexp
    exact preliminary_stage_one v p hv hp i0 e he
  · push_neg at hexp
    by_cases hval : ∃ (i : Fin 3) (g : G), (3 / 4 : ℝ) * MMS 3 (v i) p ≤ v i g
    · -- Stage 2 of the preliminary phase: some agent values a good highly.
      obtain ⟨a, e, he⟩ := hval
      exact preliminary_stage_two v p hv hp (fun i g => hexp i g) a e he
    · -- After the preliminary phase: no big goods.
      push_neg at hval
      refine exists_threequarter_MMS_three_nobig' v p hv hp (fun i g => ?_)
      exact max_lt (hexp i g) (hval i g)
end FairSelling
