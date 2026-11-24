-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.stepL_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:51:50.76044+00:00
-- url     : https://prove2.me/submissions/7f58f8f6-679f-4368-bdc3-735cb017ba40

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {u : ℂ} {c d : Fin (2 * r + k + 1)} {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j) :
    WOK (stepL k r u c d L) (j + 1) := by
  intro cw hcw
  have hmem : cw ∈ (if c = d then L.map (fun cw => (u * cw.1, cw.2)) else []) ∨
      cw ∈ L.map (fun cw => (cw.1, Xa k r c d :: cw.2)) ∨
      cw ∈ (L.map fun cw => (cw.1, Xb k r c d :: cw.2)).map fun cw => (Complex.I * cw.1, cw.2) := by
    simpa only [stepL, List.mem_append, or_assoc] using hcw
  rcases hmem with h | h | h
  · by_cases hcd : c = d
    · rw [if_pos hcd] at h
      obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 h
      obtain ⟨h1, h2⟩ := hL cw' hcw'
      exact ⟨h1, Nat.le_succ_of_le h2⟩
    · rw [if_neg hcd] at h
      simp at h
  · obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2⟩ := hL cw' hcw'
    refine ⟨?_, by simpa using h2⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact Xa_lie c d
    · exact h1 X hX
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2⟩ := hL cw' hcw'
    refine ⟨?_, by simpa using h2⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact Xb_lie c d
    · exact h1 X hX
end Formalism.FourierDecayAlt.P.JFxB
