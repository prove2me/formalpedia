-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.singleton_subset_detSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:50.455877+00:00
-- url     : https://prove2.me/submissions/57032d93-6363-4cb6-9070-4a3e3921a85f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

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
theorem _root_.solution {m : ℕ} {Kc : Set ℂ} {D : ℂ} (hD : D ∈ Kc) :
    ({(wMat (m + 1)).det * D} : Set ℂ) ⊆ detSet (m + 1) Kc := by
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  exact ⟨D, hD, hw.symm⟩
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
