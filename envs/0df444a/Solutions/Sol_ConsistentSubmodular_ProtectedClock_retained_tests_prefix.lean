-- Prove2me | solution 1 for ConsistentSubmodular.ProtectedClock.retained_tests_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:51.080425+00:00
-- url     : https://prove2.me/submissions/654f968b-3041-4b91-baa1-8eed408bd14d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows
import Theorems.Thm_ConsistentSubmodular_FractionalWindow_retained_tests_extend

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

namespace Objective

variable (f : Objective n)

/-- Every competitor's new part is already in the window buffer. -/
theorem value_le_windowOptimum {N E A : Finset (Fin n)} {k : ℕ}
    (hAE : A ⊆ E) (hAk : A.card ≤ k) :
    f.value A ≤ f.bufferedOptimum N (E \ N) k := by
  have hsub : A ⊆ (E \ N) ∪ (A ∩ N) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    by_cases heN : e ∈ N
    · exact Or.inr ⟨he, heN⟩
    · exact Or.inl ⟨hAE he, heN⟩
  exact (f.monotone A _ hsub).trans
    (f.le_bufferedOptimum Finset.inter_subset_right
      ((Finset.card_le_card Finset.inter_subset_left).trans hAk))

theorem optimum_le_windowOptimum (N E : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimum E ∅ k ≤ f.bufferedOptimum N (E \ N) k := by
  have hA := f.bufferedOptimizer_spec E ∅ k
  simpa [bufferedOptimum] using f.value_le_windowOptimum hA.1 hA.2.1

end Objective

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

namespace ProtectedClock

variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)

theorem windowBuffer_absolute (n i t : ℕ) (ht : C.start i ≤ t) :
    C.windowBuffer n i (t - C.start i) = arrivedPrefix n t\arrivedPrefix n (C.start i) := by
  simp [windowBuffer, windowOld, Nat.add_sub_of_le ht]

variable {n : ℕ} (f : Objective n) (κ : ℕ)

/-- Every actual-time prefix competitor fits inside the old core plus new buffer. -/
theorem window_benchmark_dominates (i u : ℕ) :
    f.prefixOptimum κ (C.start i + u) ≤
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i u) κ :=
  f.optimum_le_windowOptimum (C.windowOld n i) (arrivedPrefix n (C.start i + u)) κ

theorem window_benchmark_absolute (i t : ℕ) (ht : C.start i ≤ t) :
    f.prefixOptimum κ t ≤
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i (t - C.start i)) κ := by
  have hh := C.window_benchmark_dominates f κ i (t - C.start i)
  rwa [Nat.add_sub_of_le ht] at hh

end ProtectedClock

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)
variable {n : ℕ} (f : Objective n) (κ : ℕ)

theorem solution (O : CertificateFamily) (N : ℕ) (hN : 0 < N) (i : ℕ)
    (A : Finset (Fin n))
    (htests : ∀ j, let W := C.fractionalWindows f κ O N hN i
      O.level * f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i (W.retained j)) κ-
        f.prefixOptimum κ (C.start i) / N ≤ f.value (C.windowBuffer n i (W.retained j) ∪ A)) :
    ∀ t, C.start i ≤ t → t ≤ C.start (i + 1) →
      (O.level - 2 / N) * f.prefixOptimum κ t ≤
        f.value (A ∪ (arrivedPrefix n t\arrivedPrefix n (C.start i))) := by
  let W := C.fractionalWindows f κ O N hN i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hη : 0 ≤ (1 : ℝ) / N := div_nonneg (by norm_num) hNr.le
  have hV : 0 ≤ f.prefixOptimum κ (C.start i) := f.prefixOptimum_nonnegative _ _
  have hext := W.retained_tests_extend hN A (f.prefixOptimum κ (C.start i) / N)
    (div_nonneg hV hNr.le) htests
  intro t ht0 ht1
  have hu : t - C.start i ≤ C.windowDuration i := Nat.sub_le_sub_right ht1 _
  have hg := hext (t - C.start i) hu
  have hbench := C.window_benchmark_absolute f κ i t ht0
  rw [C.windowBuffer_absolute n i t ht0] at hbench
  have hmono := f.prefixOptimum_monotone κ ht0
  have hscale : f.bufferedOptimum (C.windowOld n i) ∅ κ = f.prefixOptimum κ (C.start i) := rfl
  rw [hscale, C.windowBuffer_absolute n i t ht0, Finset.union_comm] at hg
  have hdiv := div_le_div_of_nonneg_right hmono hNr.le
  have hcur : 0 ≤ f.prefixOptimum κ t / N := div_nonneg (f.prefixOptimum_nonnegative _ _) hNr.le
  have hid : (O.level - 2 / N) * f.prefixOptimum κ t =
      O.level * f.prefixOptimum κ t - 2 * (f.prefixOptimum κ t / N) := by ring
  have hbench' := mul_le_mul_of_nonneg_left hbench O.level_nonneg
  have hdiv' := mul_le_mul_of_nonneg_left hdiv O.level_nonneg
  have hle := mul_le_mul_of_nonneg_right O.level_le (show 0 ≤ f.prefixOptimum κ (C.start i) / N by
    exact div_nonneg (f.prefixOptimum_nonnegative _ _) hNr.le)
  rw [hid]
  nlinarith only [hg, hbench', hdiv, hdiv', hcur, hle, mul_nonneg O.level_nonneg
    (div_nonneg (f.prefixOptimum_nonnegative κ (C.start i)) hNr.le)]

end
