-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.abs_nonstationaryCutoff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:37.735017+00:00
-- url     : https://prove2.me/submissions/ab396c15-5547-4f2e-9a37-78cca1704fe1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_critCut_mem_Icc

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
theorem _root_.solution (m : ℕ) (δ : ℝ) (D : ℂ) (x : Fin (m + 1) → ℂ) :
    |farCut m δ D x| ≤ 1 + ((rootSet (m + 2) ((-1) ^ (m + 3) * D)).card : ℝ) := by
  unfold farCut
  have h1 : 0 ≤ ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), critCut δ z x :=
    Finset.sum_nonneg fun z _ => (critCut_mem_Icc δ z x).1
  have h2 : ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), critCut δ z x ≤
      ((rootSet (m + 2) ((-1) ^ (m + 3) * D)).card : ℝ) := by
    calc _ ≤ ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), (1 : ℝ) :=
          Finset.sum_le_sum fun z _ => (critCut_mem_Icc δ z x).2
      _ = _ := by simp
  rw [abs_le]; constructor <;> linarith
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
