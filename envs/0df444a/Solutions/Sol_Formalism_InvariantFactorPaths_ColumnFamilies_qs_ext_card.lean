-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ext_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:39.588119+00:00
-- url     : https://prove2.me/submissions/2973768f-f20e-49a6-8f6c-eaca6112dda4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_low
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_colH_high

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) (c : ℤ) :
    (qs_ext mu I c).card = colH mu c := by
  unfold qs_ext
  split_ifs with h1 h2
  · exact (I ⟨c, h1⟩).2
  · rw [qs_colH_low hmu h2]; simp
  · rw [qs_colH_high hmu (by simp only [TCols, mem_Ioc] at h1; omega)]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
