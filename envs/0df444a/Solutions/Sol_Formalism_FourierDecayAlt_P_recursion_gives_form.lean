-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.recursion_gives_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:27.435281+00:00
-- url     : https://prove2.me/submissions/afc89b5b-5af2-4329-aa04-37792af8d182

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
theorem _root_.solution : Formalism.FourierDecayAlt.J.RecursionGivesForm := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', h⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B he1 hI hδ hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hyp
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = B.e1 := by
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ D.r + 1),
      Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), one_mul, he1]
  have key := hS ((1 + B.δ) * B.e1 * B.IntN) (fun R => by
    have := h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
    rw [hprod] at this
    rw [hδ, hI]; exact this)
  calc B.c0 * B.c0' * B.KV ≤ B.n0c * ((1 + B.δ) * B.e1 * B.IntN) := key
    _ = _ := by ring
end Formalism.FourierDecayAlt.P
