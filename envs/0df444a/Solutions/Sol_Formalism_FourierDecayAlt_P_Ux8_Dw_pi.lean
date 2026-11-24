-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.Dw_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:52:19.157805+00:00
-- url     : https://prove2.me/submissions/4dd25ea5-5bf3-4b3a-8c16-16078414c26d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_Dx_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {F : B.Mat k r → ι → E}
    (hF : B.CkOn w.length (B.GV k r) F) : ∀ g ∈ B.GV k r, ∀ i, Dw w F g i = Dw w (fun g => F g i) g := by
  induction w with
  | nil => intro g _ i; rfl
  | cons x w ih =>
    intro g hg i
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by simp
    have e : (((x :: w).length : ℕ) : ℕ∞) = 1 + w.length := by simp [add_comm]
    have h1 : B.CkOn 1 (B.GV k r) (Dw w F) := CkOn_Dw hw' (by rw [← e]; exact hF)
    show Dx x (Dw w F) g i = Dx x (Dw w fun g => F g i) g
    rw [Dx_pi (hw x (by simp)) h1 g hg i]
    exact Dx_congr (hw x (by simp)) (fun g hg => ih hw' (sCkOn_mono hle hF) g hg i) g hg
end Formalism.FourierDecayAlt.P.Ux8
