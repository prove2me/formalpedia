-- Prove2me | solution 1 for BBBV.RandomOracle.fails_one_of_close
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:40:46.121006+00:00
-- url     : https://prove2.me/submissions/1c3c284e-a68b-47c3-ac61-696a3167ee19

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

private theorem prob_close {ι : Type} [Fintype ι] (u v : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (ε : ℝ) (h : ‖u - v‖ ≤ ε) :
    ∑ c, |‖u c‖ ^ 2 - ‖v c‖ ^ 2| ≤ 4 * ε := by
  classical
  let U : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ‖u i‖)
  let V : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ‖v i‖)
  let D : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ‖(u - v) i‖)
  have hU : ‖U‖ = 1 := by
    have hs : ‖U‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    nlinarith [norm_nonneg U]
  have hV : ‖V‖ = 1 := by
    have hs : ‖V‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    nlinarith [norm_nonneg V]
  have hD : ‖D‖ = ‖u - v‖ := by
    have hs : ‖D‖ ^ 2 = ‖u - v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    nlinarith [norm_nonneg D, norm_nonneg (u - v)]
  have hb : (∑ c, |‖u c‖ ^ 2 - ‖v c‖ ^ 2|) ≤ inner ℝ D (U + V) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_le_sum
    intro c hc
    simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
      WithLp.ofLp_add, Pi.add_apply]
    rw [mul_comm]
    change |‖u c‖ ^ 2 - ‖v c‖ ^ 2| ≤ ‖u c - v c‖ * (‖u c‖ + ‖v c‖)
    calc
      _ = |‖u c‖ - ‖v c‖| * (‖u c‖ + ‖v c‖) := by
        rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ← abs_mul]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
  have hn : ‖U + V‖ ≤ 2 := by
    have hh := norm_add_le U V
    rw [hU, hV] at hh
    norm_num at hh ⊢
    exact hh
  have he : 0 ≤ ε := (norm_nonneg _).trans h
  calc
    _ ≤ inner ℝ D (U + V) := hb
    _ ≤ ‖D‖ * ‖U + V‖ := real_inner_le_norm _ _
    _ ≤ ‖u - v‖ * 2 := by rw [hD]; gcongr
    _ ≤ 4 * ε := by nlinarith

namespace BBBV.RandomOracle

private theorem state_unit {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : QueryAlg (Str n) (Str n) W T) (g : Fin T → Str n → Str n) (i : ℕ) :
    ‖state M g i‖ = 1 := by
  induction i with
  | zero => exact M.init_norm
  | succ i ih => simp only [state]; split <;> simp_all

end BBBV.RandomOracle

namespace BBBV.RandomOracle

theorem fails_one_of_close {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : QueryAlg (Str n) (Str n) W T) (A : Str n → Str n) (hA : NoInverse A) (y : Str n)
    (h : ‖final M (fun _ => A) - final M (fun _ => Function.update A y (ones n))‖ ≤ 1 / 13) :
    ¬ (Decides M (fun _ => A) (∃ x, A x = ones n) ∧
      Decides M (fun _ => Function.update A y (ones n))
        (∃ x, Function.update A y (ones n) x = ones n)) := by
  classical
  intro hd
  have hno : ¬ ∃ x, A x = ones n := by
    rintro ⟨z, hz⟩
    exact hA z hz
  have hyes : ∃ x, Function.update A y (ones n) x = ones n := ⟨y, by simp⟩
  have h₁ := hd.1.2 hno
  have h₂ := hd.2.1 hyes
  have hh := prob_close (final M (fun _ => A))
    (final M (fun _ => Function.update A y (ones n)))
    (state_unit M _ T) (state_unit M _ T) (1 / 13) h
  have hs : |acceptProb M (fun _ => A) -
      acceptProb M (fun _ => Function.update A y (ones n))| ≤ 4 * (1 / 13) := by
    unfold acceptProb
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ c ∈ M.accept, |‖final M (fun _ => A) c‖ ^ 2 -
          ‖final M (fun _ => Function.update A y (ones n)) c‖ ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, |‖final M (fun _ => A) c‖ ^ 2 -
          ‖final M (fun _ => Function.update A y (ones n)) c‖ ^ 2| :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => abs_nonneg _)
      _ ≤ _ := hh
  have := (abs_le.mp hs).1
  norm_num at this
  linarith


end BBBV.RandomOracle

open BBBV.RandomOracle

theorem solution {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (M : QueryAlg (Str n) (Str n) W T) (A : Str n → Str n) (hA : NoInverse A) (y : Str n)
    (h : ‖final M (fun _ => A) - final M (fun _ => Function.update A y (ones n))‖ ≤ 1 / 13) :
    ¬ (Decides M (fun _ => A) (∃ x, A x = ones n) ∧
      Decides M (fun _ => Function.update A y (ones n))
        (∃ x, Function.update A y (ones n) x = ones n)) := BBBV.RandomOracle.fails_one_of_close M A hA y h


#print axioms solution

