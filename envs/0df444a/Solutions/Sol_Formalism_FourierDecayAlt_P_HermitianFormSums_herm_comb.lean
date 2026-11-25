-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormSums.herm_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:55:04.053819+00:00
-- url     : https://prove2.me/submissions/8ae26348-4e25-4212-ae40-8537a9944038

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormSums_herm_lsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormSums_herm_rsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.HermitianFormSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormSums
theorem _root_.solution {m : ℕ} {vs : List (Fin (2 * r + k + 1) → ℂ)} {C : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hC : IsFrameOf k r vs C) (f g : Fin m → ℂ) :
    herm (Hpk k r) (∑ a, f a • C a) (∑ b, g b • C b) = ∑ a, f a * star (g a) := by
  rw [herm_lsum]
  apply Finset.sum_congr rfl
  intro a _
  rw [herm_rsum]
  simp only [hC.2.1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end Formalism.FourierDecayAlt.P.HermitianFormSums
