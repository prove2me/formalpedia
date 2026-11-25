-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.ccleQ_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:22.871651+00:00
-- url     : https://prove2.me/submissions/f97e5490-0549-40ac-95ef-1c23761dd9d8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutNFApxDomThQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutBP
theorem _root_.solution {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b : ℝ} (h : B.CCle A m F b) : 0 ≤ b := by
  obtain ⟨g, hg⟩ : ∃ g, g ∈ B.GV k r := ⟨1, by simp [B.GV, Formalism.QuantumDeterminants.UH]⟩
  have h1 := h.2 [] [] (by simp) (by simp) (by simp) g hg
  have h2 : 0 ≤ B.gN g ^ A * ‖B.dLR [] [] F g‖ :=
    mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
  linarith
end Formalism.FourierDecayAlt.P.CutBP
