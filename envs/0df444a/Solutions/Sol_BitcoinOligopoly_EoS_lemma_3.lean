-- Prove2me | solution 1 for BitcoinOligopoly.EoS.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:23:59.365633+00:00
-- url     : https://prove2.me/submissions/6c6b3a75-57d1-4a04-b374-1605033615a3

import Mathlib
import Definitions.Def_BitcoinOligopoly_EoS_Model

set_option autoImplicit false
open BitcoinOligopoly.EoS

namespace EoSAux

variable {n : ℕ}

lemma nonneg_of_eq {P : Params n} {q : Fin n → ℝ} (hq : IsEquilibrium P q) (i : Fin n) :
    0 ≤ q i := hq.1 i

lemma dev {P : Params n} {q : Fin n → ℝ} (hq : IsEquilibrium P q) (i : Fin n) (t : ℝ)
    (ht : 0 ≤ t) : utility P (Function.update q i t) i ≤ utility P q i := hq.2 i t ht

lemma sum_eq_add (P : Params n) (q : Fin n → ℝ) (i : Fin n) :
    ∑ j, q j ^ P.α = q i ^ P.α + ∑ j ∈ Finset.univ.erase i, q j ^ P.α :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

lemma sum_update (P : Params n) (q : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ∑ j, (Function.update q i t) j ^ P.α = t ^ P.α + ∑ j ∈ Finset.univ.erase i, q j ^ P.α := by
  rw [sum_eq_add P _ i, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma R_nonneg {P : Params n} {q : Fin n → ℝ} (hq : IsEquilibrium P q) (i : Fin n) :
    0 ≤ ∑ j ∈ Finset.univ.erase i, q j ^ P.α :=
  Finset.sum_nonneg fun j _ => Real.rpow_nonneg (nonneg_of_eq hq j) _

lemma utility_update (P : Params n) (q : Fin n → ℝ) (i : Fin n) (t : ℝ) (ht : 0 < t)
    (hR : 0 ≤ ∑ j ∈ Finset.univ.erase i, q j ^ P.α) :
    utility P (Function.update q i t) i =
      t ^ P.α / (t ^ P.α + ∑ j ∈ Finset.univ.erase i, q j ^ P.α) - P.c i * t := by
  have hp : 0 < t ^ P.α := Real.rpow_pos_of_pos ht _
  unfold utility share
  rw [sum_update, if_neg (by positivity), Function.update_self]

lemma S_pos {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q) :
    0 < ∑ j, q j ^ P.α := by
  obtain ⟨hn, hα, hc⟩ := hP
  have hα0 : 0 < P.α := by linarith
  have hnn : ∀ j, 0 ≤ q j ^ P.α := fun j => Real.rpow_nonneg (nonneg_of_eq hq j) _
  rcases (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hnn j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : ∀ j, q j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 h.symm j (Finset.mem_univ j)
      exact ((Real.rpow_eq_zero_iff_of_nonneg (nonneg_of_eq hq j)).1 this).1
    let i : Fin n := ⟨0, by omega⟩
    have hci := hc i
    set t : ℝ := 1 / (2 * P.c i) with ht
    have ht0 : 0 < t := by positivity
    have hR : ∑ j ∈ Finset.univ.erase i, q j ^ P.α = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hz j, Real.zero_rpow hα0.ne']
    have h1 := dev hq i t ht0.le
    rw [utility_update P q i t ht0 (by rw [hR]), hR] at h1
    have hp : 0 < t ^ P.α := Real.rpow_pos_of_pos ht0 _
    have h2 : utility P q i = 0 := by
      unfold utility share
      rw [h.symm, if_pos rfl, hz i]; simp
    rw [h2, add_zero, div_self hp.ne'] at h1
    have : P.c i * t = 1 / 2 := by rw [ht]; field_simp
    linarith

lemma share_eq {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i : Fin n) : share P q i = q i ^ P.α / ∑ j, q j ^ P.α := by
  unfold share
  rw [if_neg (S_pos hP hq).ne']

lemma foc {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i : Fin n) (hi : 0 < q i) :
    P.c i = P.α * q i ^ (P.α - 1) * (1 - share P q i) / (∑ j, q j ^ P.α) := by
  obtain ⟨hn, hα, hc⟩ := hP
  have hP' : P.Standing := ⟨hn, hα, hc⟩
  set R := ∑ j ∈ Finset.univ.erase i, q j ^ P.α with hR
  have hR0 : 0 ≤ R := R_nonneg hq i
  have hS : ∑ j, q j ^ P.α = q i ^ P.α + R := sum_eq_add P q i
  have hSp := S_pos hP' hq
  set g : ℝ → ℝ := fun t => t ^ P.α / (t ^ P.α + R) - P.c i * t with hg
  have hloc : IsLocalMax g (q i) := by
    filter_upwards [Ioi_mem_nhds hi] with t ht
    have h1 := dev hq i t (le_of_lt ht)
    rw [utility_update P q i t ht hR0] at h1
    have h2 : utility P q i = g (q i) := by
      have := utility_update P q i (q i) hi hR0
      rw [Function.update_eq_self] at this
      rw [this]
    rw [h2] at h1
    exact h1
  have hd : HasDerivAt g
      ((P.α * (q i) ^ (P.α - 1) * ((q i) ^ P.α + R) - (q i) ^ P.α * (P.α * (q i) ^ (P.α - 1)))
        / ((q i) ^ P.α + R) ^ 2 - P.c i) (q i) := by
    have h1 := Real.hasDerivAt_rpow_const (x := q i) (p := P.α) (Or.inl hi.ne')
    have h2 := h1.add_const R
    have h3 := h1.div h2 (by rw [← hS]; exact hSp.ne')
    have h4 : HasDerivAt (fun t : ℝ => P.c i * t) (P.c i) (q i) := by
      simpa using (hasDerivAt_id (q i)).const_mul (P.c i)
    exact h3.sub h4
  have h0 := hloc.hasDerivAt_eq_zero hd
  have h0' : P.c i = (P.α * (q i) ^ (P.α - 1) * ((q i) ^ P.α + R)
      - (q i) ^ P.α * (P.α * (q i) ^ (P.α - 1))) / ((q i) ^ P.α + R) ^ 2 := by linarith
  rw [h0', share_eq hP' hq i, hS]
  have hp : 0 < q i ^ P.α + R := by rw [← hS]; exact hSp
  field_simp

lemma lemma3_eq {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i : Fin n) : P.c i * q i = P.α * share P q i * (1 - share P q i) := by
  have hα0 : 0 < P.α := by have := hP.2.1; linarith
  rcases (nonneg_of_eq hq i).lt_or_eq with hi | hi
  · have h := foc hP hq i hi
    have hSp := S_pos hP hq
    rw [share_eq hP hq i] at h ⊢
    have hq1 : q i ^ (P.α - 1) * q i = q i ^ P.α := by
      rw [Real.rpow_sub_one hi.ne']; field_simp
    rw [h]
    field_simp
    rw [← hq1]; ring
  · rw [← hi]
    have : share P q i = 0 := by
      rw [share_eq hP hq i, ← hi, Real.zero_rpow hα0.ne']; simp
    rw [this]; simp

lemma lemma3_ineq {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i : Fin n) :
    P.α * q i ^ (P.α - 1) * (1 - share P q i) / (∑ j, q j ^ P.α) ≤ P.c i := by
  have hSp := S_pos hP hq
  have hα := hP.2.1
  have hα0 : 0 < P.α := by linarith
  have hci := hP.2.2 i
  rcases (nonneg_of_eq hq i).lt_or_eq with hi | hi
  · exact (foc hP hq i hi).ge
  · have hsh : share P q i = 0 := by
      rw [share_eq hP hq i, ← hi, Real.zero_rpow hα0.ne']; simp
    rw [hsh, ← hi]
    rcases hα.lt_or_eq with h1 | h1
    · rw [Real.zero_rpow (by linarith)]
      simp [hci.le]
    · -- α = 1
      have hS1 : (∑ j, q j ^ P.α) = ∑ j ∈ Finset.univ.erase i, q j ^ P.α := by
        rw [sum_eq_add P q i, ← hi, Real.zero_rpow hα0.ne']; simp
      set S := ∑ j, q j ^ P.α with hSdef
      have hR0 := R_nonneg hq i
      have key : ∀ t : ℝ, 0 < t → 1 ≤ P.c i * (t + S) := by
        intro t ht
        have h1' := dev hq i t ht.le
        rw [utility_update P q i t ht hR0, ← hS1, ← h1] at h1'
        have h2 : utility P q i = 0 := by
          unfold utility
          rw [share_eq hP hq i, ← hi]; simp [Real.zero_rpow hα0.ne']
        rw [h2, Real.rpow_one] at h1'
        have hts : 0 < t + S := by linarith
        rw [sub_nonpos, div_le_iff₀ hts] at h1'
        nlinarith
      have : 1 ≤ P.c i * S := by
        by_contra hlt
        push_neg at hlt
        have ht : 0 < (1 - P.c i * S) / (2 * P.c i) := by
          apply div_pos (by linarith) (by linarith)
        have := key _ ht
        have e : P.c i * ((1 - P.c i * S) / (2 * P.c i) + S) = (1 + P.c i * S) / 2 := by
          field_simp; ring
        rw [e] at this
        linarith
      rw [← h1, sub_self, Real.rpow_zero]
      rw [div_le_iff₀ hSp]
      linarith

end EoSAux

open EoSAux in
theorem solution {n : ℕ} (P : Params n) (hP : P.Standing) (q : Fin n → ℝ)
    (hq : IsEquilibrium P q) :
    (∀ i, P.c i * q i = P.α * share P q i * (1 - share P q i)) ∧
    (∀ i, P.α * q i ^ (P.α - 1) * (1 - share P q i) /
      (∑ j, q j ^ P.α) ≤ P.c i) :=
  ⟨lemma3_eq hP hq, lemma3_ineq hP hq⟩
