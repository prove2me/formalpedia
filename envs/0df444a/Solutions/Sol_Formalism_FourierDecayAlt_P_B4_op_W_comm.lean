-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.op_W_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:00:40.284236+00:00
-- url     : https://prove2.me/submissions/0a69918d-4234-41a8-beeb-3a6b47c15709

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_comm

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
theorem _root_.solution {Z : Mat k r} (hZ : inLie k r Z) (u : List (Mat k r)) (hu : ∀ X ∈ u, inLie k r X) :
    ∀ K : Mat k r → E, CkOn ((u.length + 1 : ℕ) : ℕ∞) (GV k r) K → ∀ g ∈ GV k r,
      op false Z (W (lr u []) K) g = W (lr u []) (op false Z K) g := by
  induction u with
  | nil => intro K _ g _; rfl
  | cons X u ih =>
    intro K hK g hg
    have hu' : ∀ X ∈ u, inLie k r X := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hl : AllLie (lr u ([] : List (Mat k r))) := by
      intro x hx
      simp only [lr, List.map_nil, List.append_nil, List.mem_map] at hx
      obtain ⟨Y, hY, rfl⟩ := hx
      exact hu' Y hY
    have e : ∀ K' : Mat k r → E, W (lr (X :: u) []) K' = op true X (W (lr u []) K') := fun _ => rfl
    rw [e, e, op_comm (smooth_on_of_word_derivatives _ hl 2 (ckOn_mono (by simp [lr]; omega) hK)) (hu X List.mem_cons_self) hZ hg]
    exact op_congr true (hu X List.mem_cons_self)
      (ih hu' K (ckOn_mono (by simp) hK)) g hg
end Formalism.FourierDecayAlt.P.B4
