-- Prove2me | solution 1 for EdmondsKarp.Scaling.extreme_iff_potentials
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:35:37.009688+00:00
-- url     : https://prove2.me/submissions/f68fd50c-34ea-4e3c-9e72-b228c151e92c

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

open Finset

theorem aux_eip_satur {m n : ℕ} (T : Transport m n) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (y : Flow m n) (hy : IsFlow T y) (hr : y.ret = ∑ i, T.a i) :
    (∀ i, y.f0 i = T.a i) ∧ (∀ j, y.fz j = T.b j) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hy
  constructor
  · have hs : ∑ i, y.f0 i = ∑ i, T.a i := by linarith
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => h4 i)).1 hs
    exact fun i => this i (Finset.mem_univ i)
  · have hs : ∑ j, y.fz j = ∑ j, T.b j := by linarith
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun j _ => h5 j)).1 hs
    exact fun j => this j (Finset.mem_univ j)

theorem aux_eip_ret {m n : ℕ} (hm : 1 ≤ m) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (x : Flow m n) (hx : IsMaxFlow T x) : x.ret = ∑ i, T.a i := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hmax⟩ := hx
  have hSpos : 0 < ∑ i, T.a i := by
    have : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact Finset.sum_pos (fun i _ => ha i) this
  apply le_antisymm
  · have : ∑ i, x.f0 i ≤ ∑ i, T.a i := Finset.sum_le_sum (fun i _ => h4 i)
    linarith
  · let z : Flow m n := ⟨T.a, fun i j => T.a i * T.b j / ∑ k, T.a k, T.b, ∑ k, T.a k⟩
    have hz : IsFlow T z := by
      refine ⟨fun i => (ha i).le, fun i j => ?_, fun j => (hb j).le, hSpos.le, fun i => le_rfl,
        fun j => le_rfl, by simp [z], fun i => ?_, fun j => ?_, ?_⟩
      · exact div_nonneg (mul_nonneg (ha i).le (hb j).le) hSpos.le
      · show ∑ j, T.a i * T.b j / ∑ k, T.a k - T.a i = 0
        rw [← Finset.sum_div, ← Finset.mul_sum, ← hsum, mul_div_assoc, div_self hSpos.ne',
          mul_one, sub_self]
      · show T.b j - ∑ i, T.a i * T.b j / ∑ k, T.a k = 0
        rw [← Finset.sum_div, ← Finset.sum_mul, mul_comm, mul_div_assoc, div_self hSpos.ne',
          mul_one, sub_self]
      · show ∑ k, T.a k - ∑ j, T.b j = 0
        rw [hsum, sub_self]
    exact hmax z hz

def aux_eip_valid {m n : ℕ} (x : Flow m n) (L : ℕ) (w : ℕ → Fin m) (c : ℕ → Fin n) : Prop :=
  ∀ t < L, 0 < x.fx (w (t+1)) (c t)

def aux_eip_wt {m n : ℕ} (T : Transport m n) (L : ℕ) (w : ℕ → Fin m) (c : ℕ → Fin n) : ℝ :=
  ∑ t ∈ range L, (T.d (w t) (c t) - T.d (w (t+1)) (c t))

theorem aux_eip_closed {m n : ℕ} (T : Transport m n) (x : Flow m n) (hext : IsExtreme T x)
    (L : ℕ) (w : ℕ → Fin m) (c : ℕ → Fin n) (hv : aux_eip_valid x L w c) (hcl : w L = w 0) :
    0 ≤ aux_eip_wt T L w c := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp [aux_eip_wt]
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hmin⟩ := hext
  let S : Finset (Fin m × Fin n) := univ.filter (fun p => 0 < x.fx p.1 p.2)
  have hSne : S.Nonempty := ⟨(w 1, c 0), by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv 0 hL⟩
  let δ := S.inf' hSne (fun p => x.fx p.1 p.2)
  have hδpos : 0 < δ := by
    rw [Finset.lt_inf'_iff]; intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp
  have hδle : ∀ i j, 0 < x.fx i j → δ ≤ x.fx i j := fun i j h =>
    Finset.inf'_le (fun p : Fin m × Fin n => x.fx p.1 p.2)
      (b := (i, j)) (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL
  let ε : ℝ := δ / L
  have hεpos : 0 < ε := div_pos hδpos hLpos
  have hεL : ε * L = δ := by simp only [ε]; field_simp
  let D : Fin m → Fin n → ℝ := fun i j => ∑ t ∈ range L,
    ((if w t = i ∧ c t = j then (1:ℝ) else 0) - (if w (t+1) = i ∧ c t = j then (1:ℝ) else 0))
  have hrow : ∀ i, ∑ j, D i j = 0 := by
    intro i
    simp only [D]
    rw [Finset.sum_comm]
    have : ∀ t ∈ range L, ∑ j, ((if w t = i ∧ c t = j then (1:ℝ) else 0) -
        (if w (t+1) = i ∧ c t = j then (1:ℝ) else 0)) =
        (if w t = i then 1 else 0) - (if w (t+1) = i then 1 else 0) := by
      intro t _
      rw [Finset.sum_sub_distrib]
      simp [ite_and]
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub' (fun t => if w t = i then (1:ℝ) else 0),
      hcl, sub_self]
  have hcol : ∀ j, ∑ i, D i j = 0 := by
    intro j
    simp only [D]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    rw [Finset.sum_sub_distrib]
    simp [ite_and]
  have hcostD : ∑ i, ∑ j, T.d i j * D i j = aux_eip_wt T L w c := by
    simp only [D, aux_eip_wt, Finset.mul_sum]
    have : ∀ i : Fin m, ∑ j : Fin n, ∑ t ∈ range L, T.d i j *
        ((if w t = i ∧ c t = j then (1:ℝ) else 0) - (if w (t+1) = i ∧ c t = j then (1:ℝ) else 0))
        = ∑ t ∈ range L, ∑ j : Fin n, T.d i j *
        ((if w t = i ∧ c t = j then (1:ℝ) else 0) - (if w (t+1) = i ∧ c t = j then (1:ℝ) else 0))
        := fun i => Finset.sum_comm
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [mul_sub, Finset.sum_sub_distrib]
    simp [ite_and]
  let y : Flow m n := ⟨x.f0, fun i j => x.fx i j + ε * D i j, x.fz, x.ret⟩
  have hy : IsFlow T y := by
    refine ⟨h0, fun i j => ?_, h2, h3, h4, h5, h6, fun i => ?_, fun j => ?_, h9⟩
    · show 0 ≤ x.fx i j + ε * D i j
      have hD : -(∑ t ∈ range L, (if w (t+1) = i ∧ c t = j then (1:ℝ) else 0)) ≤ D i j := by
        simp only [D]
        rw [Finset.sum_sub_distrib]
        have : 0 ≤ ∑ t ∈ range L, (if w t = i ∧ c t = j then (1:ℝ) else 0) :=
          Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num)
        linarith
      rcases (h1 i j).lt_or_eq with hpos | hzero
      · have hN : ∑ t ∈ range L, (if w (t+1) = i ∧ c t = j then (1:ℝ) else 0) ≤ L := by
          calc _ ≤ ∑ t ∈ range L, (1:ℝ) := Finset.sum_le_sum (fun t _ => by split_ifs <;> norm_num)
            _ = L := by simp
        have := hδle i j hpos
        nlinarith
      · have hN : ∑ t ∈ range L, (if w (t+1) = i ∧ c t = j then (1:ℝ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          rw [if_neg]
          rintro ⟨h1', h2'⟩
          have := hv t (Finset.mem_range.1 ht)
          rw [h1', h2'] at this
          linarith
        rw [hN] at hD
        nlinarith
    · show ∑ j, (x.fx i j + ε * D i j) - x.f0 i = 0
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrow]
      linarith [h7 i]
    · show x.fz j - ∑ i, (x.fx i j + ε * D i j) = 0
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcol]
      linarith [h8 j]
  have hc := hmin y hy rfl
  have hcy : cost T y = cost T x + ε * aux_eip_wt T L w c := by
    simp only [cost, y, mul_add, Finset.sum_add_distrib]
    rw [← hcostD, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hcy] at hc
  have : 0 ≤ ε * aux_eip_wt T L w c := by linarith
  exact (mul_nonneg_iff_of_pos_left hεpos).1 this

theorem aux_eip_lb {m n : ℕ} (T : Transport m n) (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n)
    (hext : IsExtreme T x) :
    ∀ L (w : ℕ → Fin m) (c : ℕ → Fin n), aux_eip_valid x L w c →
      -((m:ℝ) * ∑ i, ∑ j, T.d i j) ≤ aux_eip_wt T L w c := by
  have hDnn : 0 ≤ ∑ i, ∑ j, T.d i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hd i j))
  have hdle : ∀ i j, T.d i j ≤ ∑ i, ∑ j, T.d i j := fun i j =>
    (Finset.single_le_sum (fun j _ => hd i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, T.d i j)
        (fun i _ => Finset.sum_nonneg (fun j _ => hd i j)) (Finset.mem_univ i))
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro w c hv
  by_cases hLm : L ≤ m
  · have hstep : ∀ t ∈ range L, -(∑ i, ∑ j, T.d i j) ≤ T.d (w t) (c t) - T.d (w (t+1)) (c t) := by
      intro t _
      have := hd (w t) (c t)
      have := hdle (w (t+1)) (c t)
      linarith
    have h2 := Finset.sum_le_sum hstep
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    unfold aux_eip_wt
    have : (L:ℝ) ≤ m := by exact_mod_cast hLm
    nlinarith
  · push Not at hLm
    obtain ⟨p, q, hpq, hqL, hwpq⟩ : ∃ p q, p < q ∧ q ≤ L ∧ w p = w q := by
      obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun t : Fin (L+1) => w t) (by simp; omega)
      have hab' : (a:ℕ) ≠ b := fun h => hab (Fin.ext h)
      rcases lt_or_gt_of_ne hab' with h | h
      · exact ⟨a, b, h, by omega, heq⟩
      · exact ⟨b, a, h, by omega, heq.symm⟩
    -- closed subwalk
    obtain ⟨w1, hw1⟩ : ∃ w1 : ℕ → Fin m, ∀ t, w1 t = w (p + t) := ⟨_, fun _ => rfl⟩
    obtain ⟨c1, hc1⟩ : ∃ c1 : ℕ → Fin n, ∀ t, c1 t = c (p + t) := ⟨_, fun _ => rfl⟩
    have hv1 : aux_eip_valid x (q - p) w1 c1 := by
      intro t ht
      have := hv (p + t) (by omega)
      rw [hw1, hc1, ← Nat.add_assoc]
      exact this
    have hcl1 : w1 (q - p) = w1 0 := by
      rw [hw1, hw1, Nat.add_sub_cancel' hpq.le, Nat.add_zero]
      exact hwpq.symm
    have hC := aux_eip_closed T x hext (q - p) w1 c1 hv1 hcl1
    -- remaining walk
    obtain ⟨w2, hw2⟩ : ∃ w2 : ℕ → Fin m, ∀ t, w2 t = if t ≤ p then w t else w (t + (q - p)) :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨c2, hc2⟩ : ∃ c2 : ℕ → Fin n, ∀ t, c2 t = if t < p then c t else c (t + (q - p)) :=
      ⟨_, fun _ => rfl⟩
    have hv2 : aux_eip_valid x (p + (L - q)) w2 c2 := by
      intro t ht
      by_cases htp : t < p
      · rw [hw2, hc2, if_pos (by omega), if_pos htp]
        exact hv t (by omega)
      · rw [hw2, hc2, if_neg (by omega), if_neg htp]
        have := hv (t + (q - p)) (by omega)
        rw [show t + 1 + (q - p) = t + (q - p) + 1 by omega]
        exact this
    have hR := ih (p + (L - q)) (by omega) w2 c2 hv2
    -- decomposition
    have hdec : aux_eip_wt T L w c = aux_eip_wt T (q - p) w1 c1 + aux_eip_wt T (p + (L - q)) w2 c2 := by
      unfold aux_eip_wt
      have e0 : ∑ t ∈ range (p + ((q - p) + (L - q))), (T.d (w t) (c t) - T.d (w (t+1)) (c t)) =
          ∑ t ∈ range p, (T.d (w t) (c t) - T.d (w (t+1)) (c t)) +
          (∑ t ∈ range (q - p), (T.d (w (p + t)) (c (p + t)) - T.d (w (p + t + 1)) (c (p + t))) +
           ∑ t ∈ range (L - q), (T.d (w (p + ((q - p) + t))) (c (p + ((q - p) + t))) -
              T.d (w (p + ((q - p) + t) + 1)) (c (p + ((q - p) + t))))) := by
        rw [Finset.sum_range_add, Finset.sum_range_add]
      rw [show p + ((q - p) + (L - q)) = L by omega] at e0
      rw [e0]
      have e1 : ∑ t ∈ range (q - p), (T.d (w1 t) (c1 t) - T.d (w1 (t+1)) (c1 t)) =
          ∑ t ∈ range (q - p), (T.d (w (p + t)) (c (p + t)) - T.d (w (p + t + 1)) (c (p + t))) := by
        apply Finset.sum_congr rfl; intro t _
        rw [hw1, hw1, hc1, ← Nat.add_assoc]
      have e2 : ∑ t ∈ range (p + (L - q)), (T.d (w2 t) (c2 t) - T.d (w2 (t+1)) (c2 t)) =
          ∑ t ∈ range p, (T.d (w t) (c t) - T.d (w (t+1)) (c t)) +
          ∑ t ∈ range (L - q), (T.d (w (p + ((q - p) + t))) (c (p + ((q - p) + t))) -
              T.d (w (p + ((q - p) + t) + 1)) (c (p + ((q - p) + t)))) := by
        rw [Finset.sum_range_add]
        congr 1
        · apply Finset.sum_congr rfl; intro t ht
          rw [Finset.mem_range] at ht
          rw [hw2, hw2, hc2, if_pos (show t ≤ p by omega), if_pos (show t + 1 ≤ p by omega),
            if_pos ht]
        · apply Finset.sum_congr rfl; intro t _
          have hc : c2 (p + t) = c (p + ((q - p) + t)) := by
            rw [hc2, if_neg (by omega)]; congr 1; omega
          have hw' : w2 (p + t + 1) = w (p + ((q - p) + t) + 1) := by
            rw [hw2, if_neg (by omega)]; congr 1; omega
          have hw : w2 (p + t) = w (p + ((q - p) + t)) := by
            rw [hw2]
            split_ifs with h
            · have : t = 0 := by omega
              subst this
              rw [Nat.add_zero, Nat.add_zero, Nat.add_sub_cancel' hpq.le]
              exact hwpq
            · congr 1; omega
          rw [hc, hw, hw']
      rw [e1, e2]
      ring
    rw [hdec]
    linarith

theorem aux_eip_pot {m n : ℕ} (hn : 1 ≤ n) (T : Transport m n)
    (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n) (hext : IsExtreme T x) :
    ∃ u : Fin m → ℝ, ∀ i j k, 0 < x.fx i j → u i ≤ u k + (T.d k j - T.d i j) := by
  let W : Fin m → Set ℝ := fun i =>
    {r | ∃ L w c, aux_eip_valid x L w c ∧ w L = i ∧ r = aux_eip_wt T L w c}
  have hbdd : ∀ i, BddBelow (W i) := fun i => ⟨-((m:ℝ) * ∑ i, ∑ j, T.d i j), by
    rintro r ⟨L, w, c, hv, -, rfl⟩
    exact aux_eip_lb T hd x hext L w c hv⟩
  have hne : ∀ i, (W i).Nonempty := fun i =>
    ⟨0, 0, fun _ => i, fun _ => ⟨0, hn⟩, fun t ht => absurd ht (Nat.not_lt_zero t), rfl,
      by simp [aux_eip_wt]⟩
  refine ⟨fun i => sInf (W i), fun i j k hij => ?_⟩
  have key : sInf (W i) - (T.d k j - T.d i j) ≤ sInf (W k) := by
    apply le_csInf (hne k)
    rintro r ⟨L, w, c, hv, hwL, rfl⟩
    obtain ⟨w', hw'⟩ : ∃ w' : ℕ → Fin m, ∀ t, w' t = if t ≤ L then w t else i :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c' : ℕ → Fin n, ∀ t, c' t = if t < L then c t else j :=
      ⟨_, fun _ => rfl⟩
    have hv' : aux_eip_valid x (L+1) w' c' := by
      intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
      · rw [hw', hc', if_pos (show t + 1 ≤ L by omega), if_pos h]
        exact hv t h
      · subst h
        rw [hw', hc', if_neg (show ¬ (t + 1 ≤ t) by omega), if_neg (lt_irrefl t)]
        exact hij
    have hwt : aux_eip_wt T (L+1) w' c' = aux_eip_wt T L w c + (T.d k j - T.d i j) := by
      unfold aux_eip_wt
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_range] at ht
        rw [hw', hw', hc', if_pos (show t ≤ L by omega), if_pos (show t + 1 ≤ L by omega),
          if_pos ht]
      · rw [hw', hw', hc', if_pos le_rfl, if_neg (show ¬ (L + 1 ≤ L) by omega),
          if_neg (lt_irrefl L), hwL]
    have hmem : aux_eip_wt T (L+1) w' c' ∈ W i :=
      ⟨L+1, w', c', hv', by rw [hw', if_neg (show ¬ (L + 1 ≤ L) by omega)], rfl⟩
    have := csInf_le (hbdd i) hmem
    linarith
  show sInf (W i) ≤ sInf (W k) + (T.d k j - T.d i j)
  linarith

end EdmondsKarp.Scaling

open EdmondsKarp.Scaling

theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n) (hx : IsMaxFlow T x) :
    IsExtreme T x ↔
      ∃ (u0 : ℝ) (u : Fin m → ℝ) (v0 : ℝ) (v : Fin n → ℝ),
        (∀ i j, 0 ≤ u i - v j + T.d i j) ∧
        (∀ i j, 0 < u i - v j + T.d i j → x.fx i j = 0) ∧
        (∀ i, u0 > u i → x.f0 i = 0) ∧
        (∀ i, u0 < u i → x.f0 i = T.a i) ∧
        (∀ j, v j > v0 → x.fz j = 0) ∧
        (∀ j, v j < v0 → x.fz j = T.b j) := by
  have hret := aux_eip_ret hm T ha hb hsum x hx
  obtain ⟨hxa, hxb⟩ := aux_eip_satur T hsum x hx.1 hret
  have hmne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hnne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  constructor
  · intro hext
    obtain ⟨u, hu⟩ := aux_eip_pot hn T hd x hext
    let v : Fin n → ℝ := fun j => Finset.univ.inf' hmne (fun k => u k + T.d k j)
    refine ⟨Finset.univ.inf' hmne u, u, Finset.univ.sup' hnne v, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      have : v j ≤ u i + T.d i j :=
        Finset.inf'_le (fun k => u k + T.d k j) (Finset.mem_univ i)
      linarith
    · intro i j hpos
      by_contra hne
      have hxpos : 0 < x.fx i j := lt_of_le_of_ne (hx.1.2.1 i j) (Ne.symm hne)
      have : u i + T.d i j ≤ v j :=
        Finset.le_inf' _ _ (fun k _ => by have := hu i j k hxpos; linarith)
      linarith
    · intro i h
      exact absurd (Finset.inf'_le u (Finset.mem_univ i)) (not_le.2 h)
    · intro i _
      exact hxa i
    · intro j h
      exact absurd (Finset.le_sup' v (Finset.mem_univ j)) (not_le.2 h)
    · intro j _
      exact hxb j
  · rintro ⟨u0, u, v0, v, h5a, h5b, -, -, -, -⟩
    refine ⟨hx.1, fun y hy hyr => ?_⟩
    obtain ⟨hya, hyb⟩ := aux_eip_satur T hsum y hy (hyr.trans hret)
    have key : ∀ z : Flow m n, IsFlow T z → (∀ i, z.f0 i = T.a i) → (∀ j, z.fz j = T.b j) →
        ∑ j, v j * T.b j - ∑ i, u i * T.a i = ∑ i, ∑ j, (v j - u i) * z.fx i j := by
      intro z hz hza hzb
      obtain ⟨-, -, -, -, -, -, -, h7, h8, -⟩ := hz
      simp only [sub_mul, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
        congr 1
        linarith [h8 j, hzb j]
      · apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
        congr 1
        linarith [h7 i, hza i]
    have hx_eq : cost T x = ∑ i, ∑ j, (v j - u i) * x.fx i j := by
      unfold cost
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rcases (h5a i j).lt_or_eq with h | h
      · rw [h5b i j h]; ring
      · have : T.d i j = v j - u i := by linarith
        rw [this]
    have hy_ge : ∑ i, ∑ j, (v j - u i) * y.fx i j ≤ cost T y := by
      unfold cost
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      have := hy.2.1 i j
      have := h5a i j
      nlinarith
    rw [hx_eq, ← key x hx.1 hxa hxb, key y hy hya hyb]
    exact hy_ge
