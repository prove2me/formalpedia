-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x2_simpleLow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:33.767258+00:00
-- url     : https://prove2.me/submissions/389de89d-c59b-4b8c-aa45-5336456eb49f

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {n : ℕ} (l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    C2.simpleLow l = ∑ a : Fin n, l a.succ a.castSucc := by
  unfold C2.simpleLow
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [dif_pos (by have := a.isLt; simp only [Fin.coe_castSucc]; omega)]
  rfl
end Formalism.FourierDecayAlt.P
