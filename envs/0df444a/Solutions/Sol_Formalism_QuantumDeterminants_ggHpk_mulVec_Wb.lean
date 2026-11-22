-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggHpk_mulVec_Wb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:25.263802+00:00
-- url     : https://prove2.me/submissions/c1793ef3-266f-4fec-9cda-7d5021247871

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds

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
theorem _root_.solution (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v)
    (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = (if i.val = r + k then -1 else 1) * v i := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases h : i.val < r ∨ r + k < i.val
    · simp [hv i h]
    · push Not at h
      simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by first | exact ⟨h.1, h.2, rfl⟩ | exact ⟨h.1, h.2⟩ | simp [h.1, h.2])]
  · intro j _ hji
    by_cases h : j.val < r ∨ r + k < j.val
    · simp [hv j h]
    · push Not at h
      have : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by intro h'; exact hji h'.2.2.symm)]
      simp [this]
  · simp
end Formalism.QuantumDeterminants
