-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_gI_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:36.742267+00:00
-- url     : https://prove2.me/submissions/6990a014-0ca9-4375-9e66-14c5f22f06f6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_gC_mul_gI
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_gC_torus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
omit [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : (qs_gI n).transpose.map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1 : ℤ)) (1 : ℤ) := by
  have h1 : (qs_gC n).map (evGL (torusPt n)) * (qs_gI n).map (evGL (torusPt n)) = 1 := by
    rw [← Matrix.map_mul, qs_gC_mul_gI]; simp
  have h2 : (qs_gC n).map (evGL (torusPt n)) = (torusPt n).val := qs_gC_torus
  have h3 : (qs_gI n).map (evGL (torusPt n)) = (torusPt n).inv := by
    calc (qs_gI n).map (evGL (torusPt n)) = ((torusPt n).inv * (torusPt n).val) * (qs_gI n).map (evGL (torusPt n)) := by
          rw [(torusPt n).inv_val, Matrix.one_mul]
      _ = (torusPt n).inv := by rw [Matrix.mul_assoc, ← h2, h1, Matrix.mul_one]
  rw [Matrix.transpose_map, h3]
  exact Matrix.diagonal_transpose _
end Formalism.InvariantFactorPaths.ColumnFamilies
