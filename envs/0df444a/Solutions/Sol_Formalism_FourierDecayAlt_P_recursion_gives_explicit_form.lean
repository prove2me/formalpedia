-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.recursion_gives_explicit_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:55:19.377804+00:00
-- url     : https://prove2.me/submissions/9b41b012-b300-4f31-8c16-9229741439f0

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.RecursionGivesBounds := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', h⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B hI hδ hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hyp
  unfold S3.MassData.InTheoremA
  apply hS
  intro R
  have := h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
  rw [Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), mul_one] at this
  rw [hδ, hI]; exact this
end Formalism.FourierDecayAlt.P
