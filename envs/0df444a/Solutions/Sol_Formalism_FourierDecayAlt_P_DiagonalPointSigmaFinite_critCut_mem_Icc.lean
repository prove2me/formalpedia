-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.critCut_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:15.329904+00:00
-- url     : https://prove2.me/submissions/82b635c4-d24f-403d-b47e-bb5d2d7f05a6

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_smooth_cutoff_mem_unit_interval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution {n : ℕ} (δ : ℝ) (z : ℂ) (x : Fin n → ℂ) : 0 ≤ critCut δ z x ∧ critCut δ z x ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (smooth_cutoff_mem_unit_interval _).1,
    Finset.prod_le_one (fun _ _ => (smooth_cutoff_mem_unit_interval _).1) fun _ _ => (smooth_cutoff_mem_unit_interval _).2⟩
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
