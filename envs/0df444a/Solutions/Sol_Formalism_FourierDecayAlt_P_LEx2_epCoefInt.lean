-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.epCoefInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:14.939135+00:00
-- url     : https://prove2.me/submissions/bf8966ab-ddd3-4dc8-9924-e3dc9b9fd3d3

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : EpCoefInt := by
  intro h B X p N hpN hpos hMeas hNF q
  obtain ⟨n, v, C, h1, h2, h3⟩ := hNF q
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  refine h B (Fin n) _ v C p N hpN ?_ ?_ h1 h2 h3
  · unfold LE.sq
    refine Finset.measurable_sum _ fun a _ => ?_
    exact (hmd a).mul ((hmS q a).norm.pow_const 2)
  · intro ω; unfold LE.sq
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)
end Formalism.FourierDecayAlt.P.LEx2
