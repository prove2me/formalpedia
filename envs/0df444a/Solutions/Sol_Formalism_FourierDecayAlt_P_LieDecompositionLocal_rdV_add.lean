-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:47:56.129052+00:00
-- url     : https://prove2.me/submissions/4ba332c1-b380-4564-ad88-fe680d3a5ffb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_eq_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) : RdV (X + Y) Φ g = RdV X Φ g + RdV Y Φ g := by
  obtain ⟨U, Φ', hU, hgU, hc, he⟩ := hloc
  rw [rdV_eq_fderiv le_rfl hU hgU hgG hc he hX, rdV_eq_fderiv le_rfl hU hgU hgG hc he hY,
    rdV_eq_fderiv le_rfl hU hgU hgG hc he (B4.inLie_add hX hY), Matrix.mul_add, map_add]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
