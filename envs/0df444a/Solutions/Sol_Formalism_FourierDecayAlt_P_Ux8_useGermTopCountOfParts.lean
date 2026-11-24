-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.useGermTopCountOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:28.009878+00:00
-- url     : https://prove2.me/submissions/3da45056-9539-4b1b-8364-da9d4e558c19

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
theorem _root_.solution : UseGermTopCountOfParts := by
  intro hTop hBud
  obtain ⟨C₁, C₂, hT⟩ := hTop
  refine ⟨C₂, fun Ca => ?_⟩
  obtain ⟨Cc, hCc⟩ := hBud C₁ C₂ Ca
  refine ⟨Cc, ?_⟩
  intro p m β hβ σ d hd n As A A₀ hn hAs hA₀ hA Kc hKc h0
  have hkey : ∀ i : ℕ, i ≤ C₂ * (m + 2) ^ 2 →
      (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 + 2 * (((p + m + 1 : ℕ) : ℝ) + 1) ^ 2 <
        (A - (Ca : ℝ) * ((n : ℝ) ^ 2 + ((p + m + 1 : ℕ) : ℝ) ^ 3 + ((p + m + 1 : ℕ) : ℝ) * (i : ℝ))) /
          (5 * (((p + m + 1 : ℕ) : ℝ) + 1)) := by
    intro i hi
    have hb := hCc (p + m + 1) n (m + 2) As i A A₀ hn (by omega) (by omega) hAs (Nat.le_succ_of_le hi) hA₀ hA
    have hr : (0 : ℝ) ≤ (Ca : ℝ) * ((p + m + 1 : ℕ) : ℝ) ^ 2 := by positivity
    push_cast at hb hr ⊢
    linarith
  refine hT p m β hβ σ d hd _ ((C₁ : ℝ) * ((m : ℝ) + 2) ^ 2) le_rfl ?_ Kc hKc h0
  intro i hi
  have hk := hkey i hi
  have hpos : (0 : ℝ) ≤ 2 * (((p + m + 1 : ℕ) : ℝ) + 1) ^ 2 := by positivity
  have hC : (0 : ℝ) ≤ (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 := by positivity
  have he : ((p + (m + 1 + 1) : ℕ) : ℝ) = ((p + m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [he]
  exact ⟨by linarith, by linarith⟩
end Formalism.FourierDecayAlt.P.Ux8
