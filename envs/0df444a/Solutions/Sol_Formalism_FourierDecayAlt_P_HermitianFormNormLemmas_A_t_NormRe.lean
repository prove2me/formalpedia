-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A.t_NormRe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:02.178881+00:00
-- url     : https://prove2.me/submissions/e80e3a36-1353-4398-a2d5-09e314787a38

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
theorem _root_.solution : NormRe := by
  intro hN hF P _ B rd g r k f Irat Ire hin hFr
  have h1 := hN P B hin
  have h2 := hF P B rd g r k f Irat Ire hin.1 hin.2.1 hFr
  obtain ⟨hrd, hg, -, -, -⟩ := hFr
  have hvg : 0 ≤ (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) := by positivity
  calc B.Gam1 * (abelian₂ rd r k f * B.AA) * Ire = B.Gam1 * B.AA * (abelian₂ rd r k f * Ire) := by ring
    _ = (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) *
          (B.Gam1 * B.AA * ((B.c0 * B.c0')⁻¹ * B.IntN)) := by rw [h2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hvg
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.A
