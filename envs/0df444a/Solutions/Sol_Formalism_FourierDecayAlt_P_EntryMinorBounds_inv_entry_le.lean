-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EntryMinorBounds.inv_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:58.127815+00:00
-- url     : https://prove2.me/submissions/414742dd-d592-459f-8562-b61b66e010ea

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_det_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.EntryMinorBounds
namespace Formalism.FourierDecayAlt.P.EntryMinorBounds
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hdet : M.det = 1) (X : ℝ) (hX : 1 ≤ X)
    (hM : ∀ i j, ‖M i j‖ ≤ X) (i j : Fin n) : ‖M⁻¹ i j‖ ≤ (Nat.factorial n : ℝ) * X ^ (n - 1) := by
  have hinv : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [hinv, Matrix.adjugate_apply]
  have hb := det_norm_le (M.updateRow j (Pi.single i 1)) (fun r => if r = j then 1 else X) (fun r s => by
    by_cases hr : r = j
    · subst hr; rw [if_pos rfl, Matrix.updateRow_self, Pi.single_apply]; split_ifs <;> simp
    · rw [if_neg hr, Matrix.updateRow_ne hr]; exact hM r s)
  refine hb.trans (le_of_eq ?_)
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_ne' Finset.univ j, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin]
end Formalism.FourierDecayAlt.P.EntryMinorBounds
