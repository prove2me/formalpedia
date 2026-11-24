-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.bound_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:04:57.11464+00:00
-- url     : https://prove2.me/submissions/7dc84fd3-58c0-47d9-9c3e-9eed19da0bd3

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_tag
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_nrm_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_nrm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {F : Mat k r → E} {A c : ℝ} {m : ℕ} (h : CCle A m F c) (w : List (Bool × Mat k r))
    (ht : LRt (w.map Prod.fst)) (hw : AllLie w) (hl : w.length ≤ m) :
    ∀ g ∈ GV k r, gN g ^ A * ‖W w F g‖ ≤ pn w * c := by
  intro g hg
  have e : (w.map nrm).map Prod.fst = w.map Prod.fst := by
    rw [List.map_map]
    rfl
  have hb := bound_tag h (w.map nrm) (by rw [e]; exact ht)
    (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact nrm_unit (hw y hy))
    (by rw [List.length_map]; exact hl) g hg
  rw [W_nrm, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (pn_nonneg w)]
  calc gN g ^ A * (pn w * ‖W (w.map nrm) F g‖) = pn w * (gN g ^ A * ‖W (w.map nrm) F g‖) := by ring
    _ ≤ pn w * c := mul_le_mul_of_nonneg_left hb (pn_nonneg w)
end Formalism.FourierDecayAlt.P.B4
