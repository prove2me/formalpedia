-- Prove2me | solution 1 for CompositeLB.DetSmooth.xstar_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:49:56.030281+00:00
-- url     : https://prove2.me/submissions/50cf573b-f21d-44a4-aada-6f5072a739d0

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

set_option autoImplicit false

open CompositeLB.DetSmooth

lemma clb_inner_v {d k : ℕ} (v : ℕ → CompositeLB.DetLip.E d)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) :
    inner ℝ (v i) (v j) = if i = j then (1 : ℝ) else 0 := by
  have := orthonormal_iff_ite.1 hv ⟨i, by omega⟩ ⟨j, by omega⟩
  simpa [Fin.ext_iff] using this

lemma clb_coord {d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) (t : ℕ) (htk : t ≤ k + 1)
    (j : ℕ) (hj : j < t) :
    inner ℝ (xstarT a v t) (v j) = a * (1 - ((j : ℝ) + 1) / ((t : ℝ) + 1)) := by
  unfold xstarT
  rw [real_inner_smul_left, sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single j]
  · rw [clb_inner_v v hv j j (by omega) (by omega)]; simp
  · intro r hr hrj
    rw [clb_inner_v v hv r j (by have := Finset.mem_range.1 hr; omega) (by omega)]
    simp [hrj]
  · intro h; exact absurd (Finset.mem_range.2 hj) h

lemma clb_sumsq (T : ℝ) (n : ℕ) :
    ∑ r ∈ Finset.range n, (T - (r : ℝ)) ^ 2
      = (n : ℝ) * T ^ 2 - T * n * ((n : ℝ) - 1) + ((n : ℝ) - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem solution {d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (t : ℕ) (ht : 1 ≤ t) (htk : t ≤ k + 1)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ))) :
    (‖xstarT a v t‖ ^ 2 =
      a ^ 2 * ∑ r ∈ Finset.range t,
        (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) ^ 2) ∧
    ‖xstarT a v t‖ ^ 2 ≤ a ^ 2 * (t : ℝ) / 3 := by
  have hnorm : ‖xstarT a v t‖ ^ 2 =
      a ^ 2 * ∑ r ∈ Finset.range t, (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have e : xstarT a v t = a • ∑ r ∈ Finset.range t,
        (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) • v r := rfl
    calc inner ℝ (xstarT a v t) (xstarT a v t)
        = inner ℝ (a • ∑ r ∈ Finset.range t,
            (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) • v r) (xstarT a v t) := by rw [← e]
      _ = a * ∑ r ∈ Finset.range t, (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) *
            inner ℝ (v r) (xstarT a v t) := by
          rw [real_inner_smul_left, sum_inner]
          simp only [real_inner_smul_left]
      _ = a ^ 2 * ∑ r ∈ Finset.range t, (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) ^ 2 := by
          have h : ∀ r ∈ Finset.range t, (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) *
              inner ℝ (v r) (xstarT a v t) = a * (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) ^ 2 := by
            intro r hr
            rw [real_inner_comm, clb_coord a v hv t htk r (Finset.mem_range.1 hr)]
            ring
          rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
          ring
  refine ⟨hnorm, ?_⟩
  rw [hnorm]
  have hsum : ∑ r ∈ Finset.range t, (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) ^ 2
      = (t : ℝ) * (2 * t + 1) / (6 * ((t : ℝ) + 1)) := by
    have hT : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have h1 : ∀ r ∈ Finset.range t, (1 - ((r : ℝ) + 1) / ((t : ℝ) + 1)) ^ 2
        = ((t : ℝ) - r) ^ 2 / ((t : ℝ) + 1) ^ 2 := by
      intro r _
      field_simp
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_div, clb_sumsq]
    field_simp
    ring
  rw [hsum]
  have hT : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have : (t : ℝ) * (2 * t + 1) / (6 * ((t : ℝ) + 1)) ≤ (t : ℝ) / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have ha := sq_nonneg a
  calc a ^ 2 * ((t : ℝ) * (2 * t + 1) / (6 * ((t : ℝ) + 1))) ≤ a ^ 2 * ((t : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left this ha
    _ = a ^ 2 * (t : ℝ) / 3 := by ring
