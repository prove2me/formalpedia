-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.ne_of_mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:24.442499+00:00
-- url     : https://prove2.me/submissions/b698d647-3bc4-44ee-a01c-6c1399c80b07

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_ofWord_cons_plus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (st : Start A)
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (Y : ℂ) :
    ∀ w : List (Letter ℂ S), (∀ l ∈ w, l.plus = true) → Y ∈ (ofWord L st w).inv → ∀ l ∈ w, Y ≠ l.pt
  | [], _, _ => by simp
  | l :: w, hp, h => by
    rw [ofWord_cons_plus L st l w (hp l (by simp))] at h
    intro l' hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact sub_ne_zero.1 h.2.1
    · exact solution Y w (fun l'' hl => hp l'' (by simp [hl])) h.1 l' hl'
end Formalism.FourierDecayAlt.P.Fr11
