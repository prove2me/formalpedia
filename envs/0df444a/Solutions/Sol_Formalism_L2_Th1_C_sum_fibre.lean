-- Prove2me | solution 1 for Formalism.L2.Th1.C.sum_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:52.094499+00:00
-- url     : https://prove2.me/submissions/28b7c7b6-b9dd-4f61-9ef2-d9089b99f5e2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SecondCoeffConsistency

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
namespace Formalism.L2.Th1.C
theorem _root_.solution (fa : G →+ G) (wp : G → K) (al : K)
    (h : ∀ T, fa T ≠ 0 → al ^ 2 * wp (fa T) =
      wp T + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), (wp (T + P) - wp P))
    (T₀ : G) (hT₀ : fa T₀ ≠ 0) :
    ∑ T ∈ Finset.univ.filter (fun T => fa T = fa T₀), wp T =
      al ^ 2 * wp (fa T₀) + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), wp P := by
  have hsplit : ∀ f : G → K, ∑ P ∈ Finset.univ.filter (fun P => fa P = 0), f P =
      f 0 + ∑ P ∈ Finset.univ.filter (fun P => fa P = 0 ∧ P ≠ 0), f P := by
    intro f
    rw [← Finset.add_sum_erase _ _ (by simp : (0 : G) ∈ Finset.univ.filter (fun P => fa P = 0))]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext P; simp [and_comm]
  have hfib : ∑ T ∈ Finset.univ.filter (fun T => fa T = fa T₀), wp T =
      ∑ P ∈ Finset.univ.filter (fun P => fa P = 0), wp (T₀ + P) := by
    apply Finset.sum_nbij' (fun T => T - T₀) (fun P => T₀ + P)
    · intro T hT; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      rw [map_sub, hT, sub_self]
    · intro P hP; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
      rw [map_add, hP, add_zero]
    · intro T _; simp
    · intro P _; simp
    · intro T _; simp
  have h0 := h T₀ hT₀
  rw [Finset.sum_sub_distrib] at h0
  rw [hfib, hsplit (fun P => wp (T₀ + P)), add_zero, h0]
  ring
end Formalism.L2.Th1.C
