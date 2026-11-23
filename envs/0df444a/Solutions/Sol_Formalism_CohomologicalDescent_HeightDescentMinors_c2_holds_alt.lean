-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.c2_holds_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:24.127722+00:00
-- url     : https://prove2.me/submissions/87864d5d-5361-48da-8383-ce95005782b9

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_orderedProd_smul_of_scalar_actions
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_orderedProd_smul_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_largest_moved_point

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : C2 := by
  intro k _ 𝒰 _ _ V _ _ _ _ N E u lam v hup hdiag
  have hscal : ∀ j : Fin N, capA E (algebraMap k 𝒰 u - ((j : ℕ) : 𝒰)) j j • v =
      (u + lam j - ((j : ℕ) : k)) • v := by
    intro j
    have hc : algebraMap k 𝒰 u - ((j : ℕ) : 𝒰) = algebraMap k 𝒰 (u - ((j : ℕ) : k)) := by
      rw [map_sub, map_natCast]
    rw [capA, if_pos rfl, hc, add_smul, hdiag, algebraMap_smul, ← add_smul]
    congr 1
    ring
  unfold capelli
  rw [Finset.sum_smul, Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
  · rw [Equiv.Perm.sign_one, Units.val_one, one_smul]
    exact orderedProd_smul_of_scalar_actions v N _ _ (fun j => by simpa using hscal j)
  · intro σ _ hσ
    obtain ⟨j0, hlt, hfix⟩ := exists_largest_moved_point σ hσ
    rw [smul_assoc, orderedProd_smul_eq_zero v N _ (fun j => u + lam j - ((j : ℕ) : k)) j0 ?_ ?_, smul_zero]
    · show capA E (algebraMap k 𝒰 u - ((j0 : ℕ) : 𝒰)) (σ j0) j0 • v = 0
      rw [capA, if_neg (ne_of_lt hlt), add_zero]
      exact hup _ _ hlt
    · intro j hj
      show capA E (algebraMap k 𝒰 u - ((j : ℕ) : 𝒰)) (σ j) j • v = _
      rw [hfix j hj]
      exact hscal j
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.CohomologicalDescent.HeightDescentMinors
