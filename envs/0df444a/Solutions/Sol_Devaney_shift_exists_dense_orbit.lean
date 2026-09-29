-- Prove2me | solution 1 for Devaney.shift_exists_dense_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T21:08:08.585273+00:00
-- url     : https://prove2.me/submissions/e8f2515d-f686-4f1d-b505-6b100d6a4cc7

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DevFix

open Devaney Devaney.Sigma2

theorem dist_eq (s t : Sigma2) : dist s t = ∑' i, distTerm s t i := rfl

theorem entry_ne (s t : Sigma2) (i : ℕ) (h : s i ≠ t i) : s.entry i ≠ t.entry i := fun he =>
  h (Fin.ext (Nat.cast_injective he))

theorem distTerm_eq_zero (s t : Sigma2) (i : ℕ) (h : s i = t i) : distTerm s t i = 0 := by
  simp [distTerm, entry, h]

theorem iterate_shift (n : ℕ) (s : Sigma2) : shift^[n] s = fun k => s (k + n) := by
  induction n generalizing s with
  | zero => funext k; simp
  | succ n ih =>
    funext k
    rw [Function.iterate_succ_apply, ih]
    show s (k + n + 1) = s (k + (n + 1))
    ring_nf

theorem dist_le_of_agree (s t : Sigma2) (n : ℕ) (h : ∀ i ≤ n, s i = t i) :
    dist s t ≤ 1 / 2 ^ n := by
  have hzero : ∑ i ∈ Finset.range (n + 1), distTerm s t i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp [distTerm, entry, h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hsplit := (summable_distTerm s t).sum_add_tsum_nat_add (n + 1)
  rw [hzero, zero_add] at hsplit
  have hsummable : Summable (fun i => distTerm s t (i + (n + 1))) :=
    (summable_distTerm s t).comp_injective (add_left_injective (n + 1))
  have hg : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + (n + 1))) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).mul_right ((1/2 : ℝ) ^ (n + 1))
  have hshow : dist s t = ∑' i, distTerm s t (i + (n + 1)) := by
    show (∑' i, distTerm s t i) = _
    rw [← hsplit]
  rw [hshow]
  calc ∑' i, distTerm s t (i + (n + 1))
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (n + 1)) :=
        Summable.tsum_le_tsum (fun i => distTerm_le s t _) hsummable hg
    _ = 1 / 2 ^ n := by
        rw [show (fun i : ℕ => (1/2:ℝ) ^ (i + (n+1))) = fun i : ℕ => (1/2:ℝ) ^ (n+1) * (1/2)^i from
          by funext i; rw [pow_add, mul_comm]]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        rw [pow_succ]
        norm_num
        rw [← inv_pow]
        ring

theorem exists_half_pow_lt {r : ℝ} (hr : 0 < r) : ∃ n : ℕ, (1 : ℝ) / 2 ^ n < r := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1/2:ℝ) < 1)
  exact ⟨n, by rwa [div_pow, one_pow] at hn⟩

/-- The finite binary word coded by `m`. -/
def wordOf (m : ℕ) : List (Fin 2) := (Encodable.decode (α := List (Fin 2)) m).getD []

/-- The length of the `m`-th block: the word coded by `m`, plus one so no block is empty. -/
def blen (m : ℕ) : ℕ := (wordOf m).length + 1

/-- The position at which the `m`-th block starts. -/
def T (m : ℕ) : ℕ := ∑ j ∈ Finset.range m, blen j

theorem T_succ (m : ℕ) : T (m + 1) = T m + blen m := Finset.sum_range_succ _ _

theorem T_mono : Monotone T := fun i j h =>
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem le_T (m : ℕ) : m ≤ T m := by
  induction m with
  | zero => simp [T]
  | succ k ih =>
    rw [T_succ]
    have h1 : 1 ≤ blen k := Nat.le_add_left 1 _
    omega

theorem blk_ex (p : ℕ) : ∃ m, p < T (m + 1) :=
  ⟨p, lt_of_lt_of_le (Nat.lt_succ_self p) (le_T (p + 1))⟩

/-- The index of the block containing position `p`. -/
def blk (p : ℕ) : ℕ := Nat.find (blk_ex p)

theorem blk_eq {m p : ℕ} (h1 : T m ≤ p) (h2 : p < T (m + 1)) : blk p = m := by
  have hle : blk p ≤ m := Nat.find_le h2
  rcases eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have hs : p < T (blk p + 1) := Nat.find_spec (blk_ex p)
    have hmono : T (blk p + 1) ≤ T m := T_mono (by omega)
    omega

/-- The sequence obtained by writing down every finite binary word in turn. -/
def star : Sigma2 := fun p => (wordOf (blk p)).getD (p - T (blk p)) 0

theorem star_block (m i : ℕ) (hi : i < blen m) :
    star (T m + i) = (wordOf m).getD i 0 := by
  have h2 : T m + i < T (m + 1) := by rw [T_succ]; omega
  have hb : blk (T m + i) = m := blk_eq (Nat.le_add_right _ _) h2
  simp [star, hb]

/-- Proposition 6.6(3). -/
theorem shift_exists_dense_orbit :
    ∃ s : Sigma2, Dense {t : Sigma2 | ∃ n : ℕ, shift^[n] s = t} := by
  refine ⟨star, ?_⟩
  rw [Metric.dense_iff]
  intro t r hr
  obtain ⟨n, hn⟩ := exists_half_pow_lt hr
  set l : List (Fin 2) := List.ofFn (fun i : Fin (n + 1) => t i) with hl
  set m : ℕ := Encodable.encode l with hm
  have hw : wordOf m = l := by simp [wordOf, hm, Encodable.encodek]
  have hll : l.length = n + 1 := by rw [hl]; simp
  refine ⟨shift^[T m] star, ?_, ⟨T m, rfl⟩⟩
  rw [Metric.mem_ball]
  refine lt_of_le_of_lt (dist_le_of_agree _ t n ?_) hn
  intro i hi
  have h1 : (shift^[T m] star) i = star (i + T m) := by rw [iterate_shift]
  have h2 : i < blen m := by rw [blen, hw, hll]; omega
  rw [h1, add_comm, star_block m i h2, hw,
    List.getD_eq_getElem l 0 (by rw [hll]; omega)]
  simp only [hl, List.getElem_ofFn]

end DevFix

open Devaney Devaney.Sigma2 in
theorem solution :
    ∃ s : Sigma2, Dense {t : Sigma2 | ∃ n : ℕ, shift^[n] s = t} :=
  DevFix.shift_exists_dense_orbit
