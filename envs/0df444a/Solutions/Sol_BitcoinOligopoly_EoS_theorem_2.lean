-- Prove2me | solution 1 for BitcoinOligopoly.EoS.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:32:52.49299+00:00
-- url     : https://prove2.me/submissions/7fbd86eb-06cf-4bbd-a59c-a5d19d5fb815

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

lemma f_anti (β : ℝ) (hβ0 : 0 ≤ β) :
    StrictAntiOn (fun x : ℝ => x ^ β * (1 - x)) (Set.Ioo (β / (1 + β)) 1) := by
  have hD : Convex ℝ (Set.Ioo (β / (1 + β)) 1) := convex_Ioo _ _
  have hpos : ∀ x ∈ Set.Ioo (β / (1 + β)) 1, 0 < x := by
    intro x hx
    exact lt_of_le_of_lt (div_nonneg hβ0 (by linarith)) hx.1
  refine strictAntiOn_of_deriv_neg hD ?_ ?_
  · intro x hx
    have := hpos x hx
    exact ((Real.continuousAt_rpow_const x β (Or.inl this.ne')).mul
      (continuousAt_const.sub continuousAt_id)).continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hx0 := hpos x hx
    have hd : HasDerivAt (fun x : ℝ => x ^ β * (1 - x))
        (β * x ^ (β - 1) * (1 - x) + x ^ β * (-1)) x := by
      have h1 := Real.hasDerivAt_rpow_const (x := x) (p := β) (Or.inl hx0.ne')
      have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      exact h1.mul h2
    rw [hd.deriv]
    have hxb : x ^ β = x ^ (β - 1) * x := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    have hlt : β * (1 - x) - x < 0 := by
      have := hx.1
      rw [div_lt_iff₀ (by linarith)] at this
      nlinarith
    have hp : 0 < x ^ (β - 1) := Real.rpow_pos_of_pos hx0 _
    rw [hxb]
    nlinarith [mul_neg_of_pos_of_neg hp hlt]

lemma f_anti' (α : ℝ) (hα : 1 ≤ α) :
    StrictAntiOn (fShape α) (Set.Ioo ((1 - 1 / α) / (1 + (1 - 1 / α))) 1) := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 ≤ 1 - 1 / α := by
    have : 1 / α ≤ 1 := by rw [div_le_one hα0]; exact hα
    linarith
  exact f_anti _ hβ0


lemma cor4 {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i : Fin n) (hs : 0 < share P q i) : 1 - 1 / P.α ≤ share P q i := by
  have hα := hP.2.1
  have hα0 : 0 < P.α := by linarith
  have hqi : 0 < q i := by
    rcases (nonneg_of_eq hq i).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [share_eq hP hq i, ← h, Real.zero_rpow hα0.ne'] at hs
      simp at hs
  have h1 := dev hq i 0 le_rfl
  have hsh : share P (Function.update q i 0) i = 0 := by
    unfold share
    rw [Function.update_self, Real.zero_rpow hα0.ne']
    simp
  unfold utility at h1
  rw [hsh, Function.update_self] at h1
  have h2 := lemma3_eq hP hq i
  have h3 : 0 ≤ share P q i * (1 - P.α * (1 - share P q i)) := by
    have : 0 ≤ share P q i - P.c i * q i := by linarith
    rw [h2] at this
    nlinarith
  have h4 : 0 ≤ 1 - P.α * (1 - share P q i) := nonneg_of_mul_nonneg_right h3 hs
  have h5 : 1 - share P q i ≤ 1 / P.α := by
    rw [le_div_iff₀ hα0]; nlinarith
  linarith

lemma c_f {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i : Fin n) (hi : 0 < q i) :
    P.c i = P.α * ((∑ j, q j ^ P.α) ^ (1 - 1 / P.α) / (∑ j, q j ^ P.α)) *
      fShape P.α (share P q i) := by
  have hα := hP.2.1
  have hα0 : 0 < P.α := by linarith
  have hSp := S_pos hP hq
  rw [foc hP hq i hi]
  have hx : share P q i = q i ^ P.α / ∑ j, q j ^ P.α := share_eq hP hq i
  have hxS : share P q i * (∑ j, q j ^ P.α) = q i ^ P.α := by
    rw [hx]; field_simp
  have hx0 : 0 ≤ share P q i := by rw [hx]; positivity
  have hqe : q i ^ (P.α - 1) =
      share P q i ^ (1 - 1 / P.α) * (∑ j, q j ^ P.α) ^ (1 - 1 / P.α) := by
    have e : P.α - 1 = P.α * (1 - 1 / P.α) := by field_simp
    rw [e, Real.rpow_mul hi.le, ← hxS, Real.mul_rpow hx0 hSp.le]
  rw [hqe]
  unfold fShape
  field_simp

lemma K_pos {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q) :
    0 < P.α * ((∑ j, q j ^ P.α) ^ (1 - 1 / P.α) / (∑ j, q j ^ P.α)) := by
  have hα0 : 0 < P.α := by have := hP.2.1; linarith
  have hSp := S_pos hP hq
  positivity

lemma share_mono {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i j : Fin n) (h : q j < q i) (hj : 0 ≤ q j) : share P q j < share P q i := by
  have hα0 : 0 < P.α := by have := hP.2.1; linarith
  have hSp := S_pos hP hq
  rw [share_eq hP hq, share_eq hP hq]
  exact div_lt_div_of_pos_right (Real.rpow_lt_rpow hj h hα0) hSp

lemma prop1_aux {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i j : Fin n) (hij : q j < q i) (hj : 0 < q j) : P.c i < P.c j := by
  have hα := hP.2.1
  have hα0 : 0 < P.α := by linarith
  have hi : 0 < q i := hj.trans hij
  have hshj : 0 < share P q j := by
    rw [share_eq hP hq]; have := S_pos hP hq; positivity
  have hlt := share_mono hP hq i j hij hj.le
  have hβ := cor4 hP hq j hshj
  have hβ0 : 0 ≤ 1 - 1 / P.α := by
    have : 1 / P.α ≤ 1 := by rw [div_le_one hα0]; exact hα
    linarith
  have hK := K_pos hP hq
  have hci := hP.2.2 i
  have hfi : fShape P.α (share P q i) < fShape P.α (share P q j) := by
    have hxi1 : share P q i < 1 := by
      by_contra hge
      push_neg at hge
      have h1 : fShape P.α (share P q i) ≤ 0 := by
        unfold fShape
        exact mul_nonpos_of_nonneg_of_nonpos
          (Real.rpow_nonneg (by linarith) _) (by linarith)
      have h2 := c_f hP hq i hi
      nlinarith
    have hjlt : (1 - 1 / P.α) / (1 + (1 - 1 / P.α)) < share P q j := by
      rw [div_lt_iff₀ (by linarith)]
      by_cases hb : 1 - 1 / P.α = 0
      · rw [hb]; simpa using hshj
      · have hbp : 0 < 1 - 1 / P.α := lt_of_le_of_ne hβ0 (Ne.symm hb)
        nlinarith
    exact f_anti' P.α hα ⟨hjlt, hlt.trans hxi1⟩ ⟨hjlt.trans hlt, hxi1⟩ hlt
  rw [c_f hP hq i hi, c_f hP hq j hj]
  exact mul_lt_mul_of_pos_left hfi hK

lemma prop1 {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i j : Fin n) (hij : q j ≤ q i) (hj : 0 < q j) :
    P.c i ≤ P.c j ∧ (P.c i = P.c j ↔ q i = q j) := by
  rcases hij.lt_or_eq with h | h
  · exact ⟨(prop1_aux hP hq i j h hj).le,
      ⟨fun hc => absurd hc (prop1_aux hP hq i j h hj).ne, fun he => absurd he.symm h.ne⟩⟩
  · have hi : 0 < q i := h ▸ hj
    have hsh : share P q i = share P q j := by
      rw [share_eq hP hq, share_eq hP hq, h]
    have hc : P.c i = P.c j := by
      rw [c_f hP hq i hi, c_f hP hq j hj, hsh]
    exact ⟨hc.le, ⟨fun _ => h.symm, fun _ => hc⟩⟩

lemma thm2 {P : Params n} (hP : P.Standing) {q : Fin n → ℝ} (hq : IsEquilibrium P q)
    (i j : Fin n) (hi : 0 < q i) (hj : 0 < q j) :
    1 - (1 / P.α) * (P.c i / P.c j) ≤ share P q i := by
  have hα := hP.2.1
  have hα0 : 0 < P.α := by linarith
  have hSp := S_pos hP hq
  have hci := hP.2.2 i
  have hcj := hP.2.2 j
  have hshi : 0 < share P q i := by rw [share_eq hP hq]; positivity
  have hshj : 0 < share P q j := by rw [share_eq hP hq]; positivity
  have hc4i := cor4 hP hq i hshi
  have hc4j := cor4 hP hq j hshj
  rcases lt_or_ge (q i) (q j) with h | h
  · have hle := (prop1 hP hq j i h.le hi).1
    have h1 : 1 ≤ P.c i / P.c j := by rw [le_div_iff₀ hcj]; linarith
    have h2 : 1 / P.α ≤ (1 / P.α) * (P.c i / P.c j) := by
      have : 0 < 1 / P.α := by positivity
      nlinarith
    linarith
  · have hx : 1 - share P q i ≤ (1 / P.α) * (P.c i / P.c j) := by
      have hfi := foc hP hq i hi
      have hfj := foc hP hq j hj
      have hj1 : P.α * (1 - share P q j) ≤ 1 := by
        have : 1 - share P q j ≤ 1 / P.α := by linarith
        rw [le_div_iff₀ hα0] at this; linarith
      have hpow : q j ^ (P.α - 1) ≤ q i ^ (P.α - 1) :=
        Real.rpow_le_rpow hj.le h (by linarith)
      have hpj : 0 ≤ q j ^ (P.α - 1) := Real.rpow_nonneg hj.le _
      have hxi : 0 ≤ 1 - share P q i := by
        have : share P q i ≤ 1 := by
          rw [share_eq hP hq, div_le_one hSp, sum_eq_add P q i]
          have := R_nonneg hq i; linarith
        linarith
      have key : P.α * (1 - share P q j) * q j ^ (P.α - 1) ≤ q i ^ (P.α - 1) := by
        calc P.α * (1 - share P q j) * q j ^ (P.α - 1) ≤ 1 * q j ^ (P.α - 1) :=
              mul_le_mul_of_nonneg_right hj1 hpj
          _ ≤ q i ^ (P.α - 1) := by linarith
      -- goal: (1-x_i) α c_j ≤ c_i
      have hmain : (1 - share P q i) * (P.α * P.c j) ≤ P.c i := by
        rw [hfi, hfj]
        have e : (1 - share P q i) * (P.α * (P.α * q j ^ (P.α - 1) * (1 - share P q j) /
            ∑ j, q j ^ P.α)) =
            ((1 - share P q i) * P.α) *
              (P.α * (1 - share P q j) * q j ^ (P.α - 1)) / ∑ j, q j ^ P.α := by
          ring
        rw [e, div_le_div_iff_of_pos_right hSp]
        have := mul_le_mul_of_nonneg_left key (mul_nonneg hxi hα0.le)
        nlinarith [this]
      rw [one_div, inv_mul_eq_div, div_div, le_div_iff₀ (by positivity)]
      calc (1 - share P q i) * (P.c j * P.α) = (1 - share P q i) * (P.α * P.c j) := by ring
        _ ≤ P.c i := hmain
    linarith

end EoSAux

open EoSAux in
theorem solution {n : ℕ} (P : Params n) (hP : P.Standing) (q : Fin n → ℝ)
    (hq : IsEquilibrium P q) (i j : Fin n) (hi : 0 < q i) (hj : 0 < q j) :
    1 - (1 / P.α) * (P.c i / P.c j) ≤ share P q i :=
  thm2 hP hq i j hi hj
