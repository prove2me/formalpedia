-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.t_NGNumbers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:40.06538+00:00
-- url     : https://prove2.me/submissions/f20f13b8-1cf6-4912-93b1-58ef00b0acd3

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D3_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
theorem _root_.solution : NGNumbers := by
  unfold NGNumbers
  intro A CB CSt Cg CT hCB hCSt hCg hCT
  refine ⟨2 + CSt + 1 + 12 + 12 * CT + Cg * A + CB + 1 + Cg, ?_, ?_⟩
  · have := mul_nonneg hCg (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
    linarith
  intro r f b rd g TT cSt e1 hS
  unfold NGSizes at hS
  obtain ⟨hf, hb, hrd0, hrd, hg1, hg, hTT0, hTT, hc0, hc, he0, he⟩ := hS
  have h := core A CB CSt Cg CT hCB hCSt hCg hCT r f b rd g TT cSt e1 (((2 * r + 2 : ℕ) : ℝ))
    (((2 * r + 2 : ℕ) : ℝ) ^ 5 * f) (by push_cast <;> ring) rfl hf hb hrd0 hrd hg1 hg hTT0 hTT hc0 hc
    he0 he
  have e : ∀ K : ℝ, K * (((2 * r + 2 : ℕ) : ℝ) ^ 5 * f) * Real.log b =
      K * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b := fun K => by ring
  rw [e, e] at h
  exact h
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
