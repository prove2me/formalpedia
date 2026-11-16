-- Prove2me | solution 1 for DetANN.HPIM.bisect_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T05:52:57.373134+00:00
-- url     : https://prove2.me/submissions/c1c9dc93-a381-413f-9030-02c849a0bc53

import Mathlib
import Definitions.Def_DetANN_HPIMFormat

namespace DetANN.HPIMBisAux

open DetANN.HPIM

variable {m : ℕ}

/-- **M5.** Binary search by power-of-two steps keeps "`lookupC lo` null, `lookupC (lo + 2^t)` not". -/
lemma bisect_spec {M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) :
    ∀ t lo, lookupC Z lo q = none → lookupC Z (lo + 2 ^ t) q ≠ none →
      lookupC Z (bisect Z q t lo - 1) q = none ∧ lookupC Z (bisect Z q t lo) q ≠ none ∧
        1 ≤ bisect Z q t lo := by
  intro t
  induction t with
  | zero =>
    intro lo h0 h1
    simp only [bisect, pow_zero] at h1 ⊢
    exact ⟨by simpa using h0, h1, by omega⟩
  | succ t ih =>
    intro lo h0 h1
    simp only [bisect]
    split_ifs with h
    · refine ih _ h ?_
      rw [add_assoc, ← two_mul, ← pow_succ']; exact h1
    · exact ih _ h0 h

lemma lookupCost_le {M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) (V : ℕ)
    (hV : ∀ i : Fin M, (Z i).visits q ≤ V) (i : ℕ) : lookupCost Z i q ≤ V := by
  unfold lookupCost; split_ifs with h
  · exact hV _
  · exact Nat.zero_le _

lemma bisectCost_le {M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) (V : ℕ)
    (hV : ∀ i : Fin M, (Z i).visits q ≤ V) : ∀ t lo, bisectCost Z q t lo ≤ t * (V + 1) + 1 := by
  intro t
  induction t with
  | zero => intro lo; simp [bisectCost]
  | succ t ih =>
    intro lo
    have h1 : lookupCCost Z (lo + 2 ^ t) q ≤ V := lookupCost_le Z q V hV _
    simp only [bisectCost]
    split_ifs
    · have := ih (lo + 2 ^ t); nlinarith
    · have := ih lo; nlinarith

end DetANN.HPIMBisAux

open DetANN.HPIM DetANN.HPIMBisAux in
theorem solution {m M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) :
    (∀ t lo, lookupC Z lo q = none → lookupC Z (lo + 2 ^ t) q ≠ none →
      lookupC Z (bisect Z q t lo - 1) q = none ∧ lookupC Z (bisect Z q t lo) q ≠ none ∧
        1 ≤ bisect Z q t lo) ∧
    ∀ V : ℕ, (∀ i : Fin M, (Z i).visits q ≤ V) →
      ∀ t lo, bisectCost Z q t lo ≤ t * (V + 1) + 1 :=
  ⟨bisect_spec Z q, fun V hV => bisectCost_le Z q V hV⟩
