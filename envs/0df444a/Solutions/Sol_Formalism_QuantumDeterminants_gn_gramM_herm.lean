-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_gramM_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:48.331784+00:00
-- url     : https://prove2.me/submissions/1aaaaa50-94ca-4cb8-8853-cabeafd9b7dc

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_eq
import Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : (gramM k r z z' g).IsHermitian := by
  have hH := gn_Hpk_herm k r
  unfold Matrix.IsHermitian at hH ⊢
  rw [gn_gramM_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
end Formalism.QuantumDeterminants
