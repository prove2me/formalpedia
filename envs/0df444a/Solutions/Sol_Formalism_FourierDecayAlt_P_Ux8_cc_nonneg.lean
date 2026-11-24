-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.cc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:59:05.784444+00:00
-- url     : https://prove2.me/submissions/dec83888-ac5c-4492-9670-615ea171f6bd

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion

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
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {f : B.Mat k r → E} {c : ℝ} (hf : B.CCle A m f c) : 0 ≤ c := by
  have h1 : (1 : B.Mat k r) ∈ B.GV k r := by
    show (1 : B.Mat k r)ᴴ * _ * 1 = _
    simp
  obtain ⟨_, h2⟩ := hf
  have h := h2 [] [] (by simp) (by simp) (by simp) 1 h1
  exact le_trans (mul_nonneg (Real.rpow_nonneg (by unfold B.gN; exact Real.sqrt_nonneg _) _) (norm_nonneg _)) h
end Formalism.FourierDecayAlt.P.Ux8
