-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggHerm_Wb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:42.974386+00:00
-- url     : https://prove2.me/submissions/a76903ce-6a15-46c5-9689-30831d7ad0e8

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Theorems.Thm_Formalism_QuantumDeterminants_ggHpk_mulVec_Wb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (z w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) :
    herm (Hpk k r) w z =
      (∑ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))).erase ⟨r + k, by omega⟩, star (z i) * w i) -
        star (z ⟨r + k, by omega⟩) * w ⟨r + k, by omega⟩ := by
  simp only [herm, dotProduct, ggHpk_mulVec_Wb k r w hw, Pi.star_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)))]
  have hs : ∑ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))).erase ⟨r + k, by omega⟩,
      star (z i) * ((if i.val = r + k then -1 else 1) * w i) =
      ∑ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))).erase ⟨r + k, by omega⟩, star (z i) * w i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_neg (fun h => (Finset.ne_of_mem_erase hi) (Fin.ext h)), one_mul]
  rw [hs, if_pos rfl]
  ring
end Formalism.QuantumDeterminants
