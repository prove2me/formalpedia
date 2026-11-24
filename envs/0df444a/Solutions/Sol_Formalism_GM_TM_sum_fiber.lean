-- Prove2me | solution 1 for Formalism.GM.TM.sum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:17.675048+00:00
-- url     : https://prove2.me/submissions/a6f73b76-65a6-4652-b0bc-c1cba8d8dd12

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open Finset
namespace Formalism.GM.TM
theorem _root_.solution {t : ℕ} (s : Fin t → Finset ℕ) (g : (Fin t → ℕ) → ℝ) (i : Fin t) :
    ∑ n ∈ Fintype.piFinset s, ∑ y ∈ s i, g (Function.update n i y) =
      (s i).card * ∑ n ∈ Fintype.piFinset s, g n := by
  classical
  rw [← Finset.sum_product' (f := fun n y => g (Function.update n i y))]
  have : ∑ x ∈ Fintype.piFinset s ×ˢ s i, g (Function.update x.1 i x.2) =
      ∑ x ∈ Fintype.piFinset s ×ˢ s i, g x.1 := by
    apply Finset.sum_nbij' (fun x => (Function.update x.1 i x.2, x.1 i)) (fun x => (Function.update x.1 i x.2, x.1 i))
    · rintro ⟨n, y⟩ h
      rw [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      dsimp only at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      by_cases hj : j = i
      · subst hj; simpa using h.2
      · rw [Function.update_of_ne hj]; exact h.1 j
    · rintro ⟨n, y⟩ h
      rw [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      dsimp only at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      by_cases hj : j = i
      · subst hj; simpa using h.2
      · rw [Function.update_of_ne hj]; exact h.1 j
    · rintro ⟨n, y⟩ _
      simp
    · rintro ⟨n, y⟩ _
      simp
    · rintro ⟨n, y⟩ _
      simp
  rw [this, Finset.sum_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.sum_const, nsmul_eq_mul]
end Formalism.GM.TM
