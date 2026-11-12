-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:33.212481+00:00
-- url     : https://prove2.me/submissions/a0042bac-1e18-47a9-a163-81bcf892649b

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction
import Theorems.Thm_GabidulinProx_UniqueDecoding_lemma_2_7

section
set_option autoImplicit false

namespace GabidulinProx.Dev.Lemma35

open GabidulinProx.UniqueDecoding

lemma eval_linearized {R : Type*} [CommSemiring R] (q : ℕ) {k : ℕ} (c : Fin k → R) (x : R) :
    (linearized q c).eval x = ∑ i, c i * x ^ (q ^ i.val) := by
  simp [linearized, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

end GabidulinProx.Dev.Lemma35

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.Lemma35

theorem chk_lemma_3_5 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (a : Fin (e + 1) → Polynomial L)
    (b : Fin (k + e) → Polynomial L)
    (hAB : GlobalIdentity (Fintype.card K) α u₀ u₁ a b)
    (z : L) (P : Polynomial L) (hP : IsLinearized (Fintype.card K) k P)
    (hclose : wordRank K (linePoint u₀ u₁ z - evaluateWord α P) ≤ e) :
    (specialize (Fintype.card K) a z).comp P + specialize (Fintype.card K) b z = 0 := by
  set q := Fintype.card K with hq
  set y := linePoint u₀ u₁ z with hy
  set A := specialize q a z with hA
  set B := linearized q (fun j => -((b j).eval z)) with hB
  have hBs : specialize q b z = -B := by
    simp only [specialize, hB, linearized, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Polynomial.monomial_neg]
  have hid : ∀ r, A.eval (y r) = B.eval (α r) := by
    intro r
    have h := congrArg (Polynomial.eval z) (hAB r)
    simp only [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero] at h
    rw [hA, hB, specialize, eval_linearized, eval_linearized]
    simp only [hy, linePoint, neg_mul, Finset.sum_neg_distrib]
    rw [eq_neg_iff_add_eq_zero]; exact h
  rw [hBs]
  by_cases hnz : A ≠ 0 ∨ B ≠ 0
  · have hrec : IsReconstruction q k e α y A B :=
      ⟨⟨_, rfl⟩, ⟨_, rfl⟩, hnz, hid⟩
    have key := (GabidulinProx.UniqueDecoding.lemma_2_7 (K := K) hk hkn hdec α hα P hP
      (y - evaluateWord α P) y (by abel) hclose).2.2.1 A B hrec
    rw [key]; simp
  · push Not at hnz
    rw [hnz.1, hnz.2]; simp

end GabidulinProx.UniqueDecoding

end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_lemma_3_5 := @GabidulinProx.UniqueDecoding.chk_lemma_3_5
