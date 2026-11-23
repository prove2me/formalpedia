-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.K_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:34.587162+00:00
-- url     : https://prove2.me/submissions/497cb52f-7462-4203-a6c5-c8d1b41529e1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_detM_diagPt
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_diagPt_norm_pos

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
theorem _root_.solution {m k : ℕ} {Kc : Set ℂ} {A K : ℝ} {Φ : Mat (m + 1 + 1) → V} {D : ℂ} (hD : D ∈ Kc)
    (h : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ) : 0 ≤ K := by
  have hmem : detM (diagPt m ((wMat (m + 1)).det * D)) ∈ detSet (m + 1) Kc := by
    rw [detM_diagPt]; exact ⟨D, hD, rfl⟩
  have h2 := (h _ hmem).2 0 (Nat.zero_le _)
  have h3 : 0 ≤ K * min 1 (‖diagPt m ((wMat (m + 1)).det * D)‖ ^ (-A)) := (norm_nonneg _).trans h2
  have h4 : 0 < min 1 (‖diagPt m ((wMat (m + 1)).det * D)‖ ^ (-A)) :=
    lt_min one_pos (Real.rpow_pos_of_pos (diagPt_norm_pos _ _) _)
  exact nonneg_of_mul_nonneg_left h3 h4
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
