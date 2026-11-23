-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.mem_inv_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:42.343341+00:00
-- url     : https://prove2.me/submissions/831f9094-0615-46c4-aafc-137cc8cf716b

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
theorem _root_.solution (P : ℂ) (hP : P ∈ st.inv) :
    ∀ w : List (Letter ℂ S), (∀ l ∈ w, l.plus = true) → (∀ l ∈ w, P - l.pt ≠ 0 ∧ P - l.pt ≠ 1) →
      P ∈ (ofWord L st w).inv
  | [], _, _ => hP
  | l :: w, hp, h => by
    rw [ofWord_cons_plus L st l w (hp l (by simp))]
    exact ⟨solution P hP w (fun l' hl => hp l' (by simp [hl])) (fun l' hl => h l' (by simp [hl])),
      h l (by simp)⟩
end Formalism.FourierDecayAlt.P.Fr11
