-- Prove2me | solution 1 for BLTCounting.AccuracySpace.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:00:00.421778+00:00
-- url     : https://prove2.me/submissions/cd66ba09-09bf-4d30-9389-43a98ec5c8c5

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

open Matrix BLTCounting.AccuracySpace

namespace AuxLemma25

lemma shifted_in_range {d m : ℕ} {c : ℕ → ℂ} {q : Fin d → ℂ}
    (hq : ∀ k, d ≤ k → c k = -∑ j : Fin d, q j * c (k - ((j : ℕ) + 1))) :
    ∀ s : ℕ, (fun r : Fin m => c ((r : ℕ) + s)) ∈
      LinearMap.range (Matrix.mulVecLin (Matrix.of fun (r : Fin m) (j : Fin d) =>
        c ((r : ℕ) + (j : ℕ)))) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hs : s < d
    · refine ⟨Pi.single ⟨s, hs⟩ 1, ?_⟩
      ext r
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · have hs : d ≤ s := Nat.le_of_not_lt hs
      have hvec : (fun r : Fin m => c ((r : ℕ) + s)) =
          -∑ j : Fin d, q j • (fun r : Fin m => c ((r : ℕ) + (s - ((j : ℕ) + 1)))) := by
        ext r
        have hdrs : d ≤ (r : ℕ) + s := le_trans hs (Nat.le_add_left s r)
        rw [hq ((r : ℕ) + s) hdrs]
        simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (j : ℕ) + 1 ≤ s := Nat.le_trans j.isLt hs
        rw [Nat.add_sub_assoc hj]
      rw [hvec]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => ?_)
      refine Submodule.smul_mem _ (q j) (ih (s - ((j : ℕ) + 1)) ?_)
      have hpos : 0 < s := lt_of_lt_of_le (Nat.zero_lt_of_lt j.isLt) hs
      omega

end AuxLemma25

theorem solution {d : ℕ} {c : ℕ → ℂ} (hc : IsBLT d c) (m : ℕ) (hm : 1 ≤ m) :
    (hankel m c).rank ≤ d := by
  have _ := hm
  rcases hc with ⟨q, hq⟩
  let M₀ : Matrix (Fin m) (Fin d) ℂ := Matrix.of fun r j => c ((r : ℕ) + (j : ℕ))
  have hsub : LinearMap.range (hankel m c).mulVecLin ≤ LinearMap.range M₀.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    have hx : (hankel m c).mulVecLin x =
        ∑ s : Fin m, x s • (fun r : Fin m => c ((r : ℕ) + (s : ℕ))) := by
      ext r
      simp [hankel, Matrix.mulVec, dotProduct, mul_comm]
    rw [hx]
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.smul_mem _ (x s) (AuxLemma25.shifted_in_range hq (s : ℕ))
  calc
    (hankel m c).rank
        = Module.finrank ℂ (LinearMap.range (hankel m c).mulVecLin) := rfl
    _ ≤ Module.finrank ℂ (LinearMap.range M₀.mulVecLin) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank ℂ (Fin d → ℂ) := LinearMap.finrank_range_le M₀.mulVecLin
    _ = d := Module.finrank_fin_fun ℂ
