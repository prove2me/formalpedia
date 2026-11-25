-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.capLft_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:25:48.924354+00:00
-- url     : https://prove2.me/submissions/339ffcba-0a00-499c-b3cc-0cac52433310

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_lZ_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_foldl_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w c : ℂ) (f : Mx k r → E) :
    capLft k r Bs w (fun x => c • f x) = fun x => c • capLft k r Bs w f x := by
  funext x
  unfold capLft qmFrev
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [foldl_smul _ c ?_ f]
  · exact smul_comm _ _ _
  · intro T hT g
    simp only [List.mem_ofFn] at hT
    obtain ⟨j, rfl⟩ := hT
    funext y
    simp only [lZ_smul, Pi.add_apply]
    split_ifs <;> simp [smul_comm c, smul_add]
end Formalism.FourierDecayAlt.P.FrameEntries
