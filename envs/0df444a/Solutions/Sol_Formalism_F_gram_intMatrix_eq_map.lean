-- Prove2me | solution 1 for Formalism.F.gram_intMatrix_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:08.872107+00:00
-- url     : https://prove2.me/submissions/9e7cc94a-0a39-4f9d-b7da-5247b7ad3720

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u
namespace Formalism.F
theorem _root_.solution {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
end Formalism.F
