-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_ScaleOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:40.169211+00:00
-- url     : https://prove2.me/submissions/785c33b9-1750-4458-aaf3-75453ad144c6

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution (hD : DiagScale) : ScaleOk := by
  intro E α _ a S F h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' x hx y hy hne
    apply h1 t t' ht ht' x hx y hy
    intro h0; apply hne; simp [scaleSys, h0]
  · intro t ht; exact hD _ _ _ a (h2 t ht)
  · intro t t' htt x hx y hy
    simp only [scaleSys]; rw [h3 t t' htt x hx y hy]
  · intro t; exact hD _ _ _ a (h4 t)
  · intro t ht
    have := hD _ _ _ a (h5 t ht)
    convert this using 3
    simp only [scaleSys]; ring
  · intro R hR
    have := hD _ _ _ a (h6 R hR)
    convert this using 3
    simp only [scaleSys]; rw [mul_sub, Finset.mul_sum]
end Formalism.FourierDecayAlt.P.Jx8
