-- Prove2me | solution 1 for BakerScudder1990.Tolerance.case2_slope
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:43:39.140803+00:00
-- url     : https://prove2.me/submissions/6d7afac5-d2a5-499f-ad29-e2673f36e14f

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

open BakerScudder1990.Tolerance in
lemma p2m_62a26528_C_add_le {n : ℕ} (I : Instance n) {i k : Fin n} (hik : i < k) :
    I.C i + I.p k ≤ I.C k := by
  unfold Instance.C
  have hk : k ∉ Finset.univ.filter (fun l : Fin n => l ≤ i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]; exact hik
  rw [add_comm, ← Finset.sum_insert hk]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    rcases hl with h | h
    · exact h ▸ le_rfl
    · exact le_trans h hik.le
  · intro l _ hl
    have hne : i ≠ l := by
      rintro rfl
      apply hl
      simp
    have := I.htol i l hne
    have := I.hu i
    have := I.hv l
    linarith


open BakerScudder1990.Tolerance BakerScudder1990.Tolerance.Instance in
theorem solution {n : ℕ} (I : Instance n) (k : Fin n) (d ε : ℝ) (hε : 0 < ε)
    (hlo : I.C k - I.v k < d) (hhi : d + ε < I.C k + I.u k) :
    I.cost (d + ε) - I.cost d =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) -
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i)) * ε := by
  unfold Instance.cost
  rw [← Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold Instance.earliness Instance.tardiness
  rcases lt_trichotomy j k with h | h | h
  · have h1 := p2m_62a26528_C_add_le I h
    have h2 := I.htol j k (ne_of_lt h)
    have := I.hu j
    have := I.hv j
    have := I.hv k
    rw [if_pos h, if_neg (not_lt.mpr h.le)]
    rw [max_eq_right (by linarith : (0:ℝ) ≤ d + ε - I.C j - I.u j),
      max_eq_right (by linarith : (0:ℝ) ≤ d - I.C j - I.u j),
      max_eq_left (by linarith : I.C j - (d + ε) - I.v j ≤ 0),
      max_eq_left (by linarith : I.C j - d - I.v j ≤ 0)]
    ring
  · subst h
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    rw [max_eq_left (by linarith : d + ε - I.C j - I.u j ≤ 0),
      max_eq_left (by linarith : d - I.C j - I.u j ≤ 0),
      max_eq_left (by linarith : I.C j - (d + ε) - I.v j ≤ 0),
      max_eq_left (by linarith : I.C j - d - I.v j ≤ 0)]
    ring
  · have h1 := p2m_62a26528_C_add_le I h
    have h2 := I.htol k j (ne_of_lt h)
    have := I.hu j
    have := I.hv j
    have := I.hu k
    rw [if_neg (not_lt.mpr h.le), if_pos h]
    rw [max_eq_left (by linarith : d + ε - I.C j - I.u j ≤ 0),
      max_eq_left (by linarith : d - I.C j - I.u j ≤ 0),
      max_eq_right (by linarith : (0:ℝ) ≤ I.C j - (d + ε) - I.v j),
      max_eq_right (by linarith : (0:ℝ) ≤ I.C j - d - I.v j)]
    ring
