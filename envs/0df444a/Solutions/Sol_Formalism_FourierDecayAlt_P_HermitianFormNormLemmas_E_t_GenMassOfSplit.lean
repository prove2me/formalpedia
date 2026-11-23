-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.t_GenMassOfSplit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:15.898683+00:00
-- url     : https://prove2.me/submissions/3850d5bd-29f8-4fc7-9c61-9f6c4d4b8a0a

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
theorem _root_.solution : Formalism.FourierDecayAlt.PN.GenMassOfSplit := by
  intro τ Rw I H H₁ _ _ _ _ _ X E _ r Cl Nu N AAre e1 Gk dens tw hA hH h γ hγ
  obtain ⟨hG, ht, hn, hd0, hd, htw, hm⟩ := h γ hγ
  have hH1 := hH γ hγ
  have hH0 : 0 ≤ N.Hh γ := by linarith
  refine ⟨by rw [hn]; positivity, hm.trans ?_⟩
  have hGk : Gk γ ≤ N.n γ * N.Hh γ ^ (6 * (2 * r + 2)) := by
    have : Gk γ = N.n γ * (tw γ)⁻¹ := by rw [hn]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left htw (by rw [hn]; positivity)
  have hn0 : 0 ≤ N.n γ := by rw [hn]; positivity
  have he1 : 0 ≤ e1 * N.Hh γ := hd0.trans hd
  calc AAre * Gk γ * dens γ * N.Hh γ ^ (10 * (r + 1) ^ 2)
      ≤ AAre * (N.n γ * N.Hh γ ^ (6 * (2 * r + 2))) * (e1 * N.Hh γ) * N.Hh γ ^ (10 * (r + 1) ^ 2) := by
        gcongr
    _ = AAre * e1 * N.Hh γ ^ eN r * N.n γ := by
        unfold eN; ring
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
