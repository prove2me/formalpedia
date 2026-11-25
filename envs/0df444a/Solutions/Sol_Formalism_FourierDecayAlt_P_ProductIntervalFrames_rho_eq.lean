-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ProductIntervalFrames.rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:37:44.805925+00:00
-- url     : https://prove2.me/submissions/58558f0a-5e4f-4fc4-8d1d-2e921d4eda16

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductIntervalFrames
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames
theorem _root_.solution (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (ρ : M.Ty (par n r T T' u)) (j : Fin n) :
    M.rho (par n r T T' u) ρ ((j : ℕ) + 1) = u ((j : ℕ) + 2) + 1 / 2 + (((ρ j : Fin _) : ℕ) : ℝ) := by
  have hj := j.isLt
  simp only [M.rho, M.Par.lo, par, max_self]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl
end Formalism.FourierDecayAlt.P.ProductIntervalFrames
