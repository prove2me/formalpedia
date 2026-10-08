-- Prove2me | solution 1 for BellmanDP.GoldMining.index_rule_n_mines
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:47:16.396752+00:00
-- url     : https://prove2.me/submissions/93cdb3f2-aa9e-41f6-a622-5f0b2945b3d3

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_MultiOutcome



namespace BellmanDP.GoldMining

open Filter Topology

lemma gm_alg1 {K : ℕ} (P Q C D : Fin K → ℝ) (xj xi t : ℝ) (A : Fin K → Fin K → ℝ) :
    ∑ k, P k * (C k * xj + ((∑ l, Q l * (D l * xi + A k l)) + t)) =
      (∑ k, P k * C k) * xj + (∑ k, P k) * ((∑ l, Q l * D l) * xi) +
        ∑ k, ∑ l, P k * Q l * A k l + (∑ k, P k) * t := by
  have h : ∀ k, P k * (C k * xj + ((∑ l, Q l * (D l * xi + A k l)) + t)) =
      P k * C k * xj + P k * ((∑ l, Q l * D l) * xi) + ∑ l, P k * Q l * A k l + P k * t := by
    intro k
    have : ∑ l, Q l * (D l * xi + A k l) = (∑ l, Q l * D l) * xi + ∑ l, Q l * A k l := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, mul_add, mul_add, mul_add, Finset.mul_sum]
    simp only [mul_assoc]; ring
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul]
lemma gm_alg2 {K : ℕ} (P Q C D : Fin K → ℝ) (xj xi : ℝ) (A : Fin K → Fin K → ℝ) :
    ∑ l, Q l * (D l * xi + ∑ k, P k * (C k * xj + A k l)) =
      (∑ l, Q l * D l) * xi + (∑ l, Q l) * ((∑ k, P k * C k) * xj) +
        ∑ k, ∑ l, P k * Q l * A k l := by
  rw [Finset.sum_comm (f := fun k l => P k * Q l * A k l)]
  have h : ∀ l, Q l * (D l * xi + ∑ k, P k * (C k * xj + A k l)) =
      Q l * D l * xi + Q l * ((∑ k, P k * C k) * xj) + ∑ k, P k * Q l * A k l := by
    intro l
    have : ∑ k, P k * (C k * xj + A k l) = (∑ k, P k * C k) * xj + ∑ k, P k * A k l := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, mul_add, mul_add, Finset.mul_sum]
    have : ∑ k, Q l * (P k * A k l) = ∑ k, P k * Q l * A k l :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [this]; ring
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul]

section Core

variable {n K : ℕ} (p c c' : Fin n → Fin K → ℝ)

noncomputable def gmIt : ℕ → (Fin n → ℝ) → ℝ
  | 0 => fun _ => 0
  | N + 1 => fun x => ⨆ i, mineOption p c c' (gmIt N) x i

def gmBox (X : Fin n → ℝ) (y : Fin n → ℝ) : Prop := ∀ j, 0 ≤ y j ∧ y j ≤ X j

lemma gm_geo_le {a b C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ∀ N : ℕ, a ≤ b + C * q ^ N) :
    a ≤ b := by
  have ht : Tendsto (fun N : ℕ => b + C * q ^ N) atTop (𝓝 (b + C * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
  simp only [mul_zero, add_zero] at ht
  exact ge_of_tendsto' ht h

lemma gm_sup_diff {ι : Type*} [Fintype ι] [Nonempty ι] (a b : ι → ℝ) (e : ℝ)
    (h : ∀ i, |a i - b i| ≤ e) : |(⨆ i, a i) - ⨆ i, b i| ≤ e := by
  have hba : BddAbove (Set.range a) := (Set.finite_range _).bddAbove
  have hbb : BddAbove (Set.range b) := (Set.finite_range _).bddAbove
  rw [abs_sub_le_iff]
  constructor
  · have : (⨆ i, a i) ≤ (⨆ i, b i) + e := ciSup_le fun i => by
      have := (abs_sub_le_iff.1 (h i)).1
      have := le_ciSup hbb i
      linarith
    linarith
  · have : (⨆ i, b i) ≤ (⨆ i, a i) + e := ciSup_le fun i => by
      have := (abs_sub_le_iff.1 (h i)).2
      have := le_ciSup hba i
      linarith
    linarith

variable (hp : ∀ i k, 0 ≤ p i k) (hc0 : ∀ i k, 0 ≤ c i k) (hc1 : ∀ i k, c i k ≤ 1)
  (hc' : ∀ i k, c i k + c' i k = 1)

include hc1 hc' in
lemma gm_upd_nonneg (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (i : Fin n) (k : Fin K) :
    ∀ j, 0 ≤ Function.update x i (c' i k * x i) j := by
  intro j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]
    have : 0 ≤ c' j k := by linarith [hc1 j k, hc' j k]
    exact mul_nonneg this (hx j)
  · rw [Function.update_of_ne hj]; exact hx j

include hc0 hc' in
lemma gm_upd_le (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (i : Fin n) (k : Fin K) :
    ∀ j, Function.update x i (c' i k * x i) j ≤ x j := by
  intro j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]
    have : c' j k ≤ 1 := by linarith [hc0 j k, hc' j k]
    nlinarith [hx j]
  · rw [Function.update_of_ne hj]

include hc0 hc1 hc' in
lemma gm_upd_box (X x : Fin n → ℝ) (hx : gmBox X x) (i : Fin n) (k : Fin K) :
    gmBox X (Function.update x i (c' i k * x i)) := by
  have hx0 : ∀ j, 0 ≤ x j := fun j => (hx j).1
  intro j
  exact ⟨gm_upd_nonneg c c' hc1 hc' x hx0 i k j,
    (gm_upd_le c c' hc0 hc' x hx0 i k j).trans (hx j).2⟩

include hc0 hc' in
lemma gm_W_upd (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (i : Fin n) (k : Fin K) :
    ∑ j, Function.update x i (c' i k * x i) j ≤ ∑ j, x j :=
  Finset.sum_le_sum fun j _ => gm_upd_le c c' hc0 hc' x hx i k j

lemma gm_opt_split (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    mineOption p c c' u x i = (∑ k, p i k * c i k) * x i +
      ∑ k, p i k * u (Function.update x i (c' i k * x i)) := by
  unfold mineOption
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

include hp in
lemma gm_opt_diff (u v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) (q e : ℝ)
    (hq : ∑ k, p i k ≤ q) (he : 0 ≤ e)
    (h : ∀ k, |u (Function.update x i (c' i k * x i)) - v (Function.update x i (c' i k * x i))| ≤ e) :
    |mineOption p c c' u x i - mineOption p c c' v x i| ≤ q * e := by
  rw [gm_opt_split, gm_opt_split]
  have : (∑ k, p i k * u (Function.update x i (c' i k * x i))) -
      ∑ k, p i k * v (Function.update x i (c' i k * x i)) =
      ∑ k, p i k * (u (Function.update x i (c' i k * x i)) - v (Function.update x i (c' i k * x i))) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun k _ => by ring
  calc _ = |∑ k, p i k * (u (Function.update x i (c' i k * x i)) - v (Function.update x i (c' i k * x i)))| := by
        rw [← this]; ring_nf
    _ ≤ ∑ k, |p i k * (u (Function.update x i (c' i k * x i)) - v (Function.update x i (c' i k * x i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, p i k * e := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, abs_of_nonneg (hp i k)]; exact mul_le_mul_of_nonneg_left (h k) (hp i k)
    _ = (∑ k, p i k) * e := by rw [Finset.sum_mul]
    _ ≤ q * e := mul_le_mul_of_nonneg_right hq he


lemma gm_it_ge (N : ℕ) (y : Fin n → ℝ) (m : Fin n) :
    mineOption p c c' (gmIt p c c' N) y m ≤ gmIt p c c' (N + 1) y :=
  le_ciSup (f := fun i => mineOption p c c' (gmIt p c c' N) y i) (Set.finite_range _).bddAbove m

lemma gm_it_eq (hn : 0 < n) (N : ℕ) (y : Fin n → ℝ) :
    ∃ m, gmIt p c c' (N + 1) y = mineOption p c c' (gmIt p c c' N) y m := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨m, hm⟩ := exists_eq_ciSup_of_finite (f := fun i => mineOption p c c' (gmIt p c c' N) y i)
  exact ⟨m, hm.symm⟩

include hp hc0 hc1 hc' in
lemma gm_cauchy (hn : 0 < n) (q : ℝ) (hq : ∀ i, ∑ k, p i k ≤ q) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∀ N : ℕ, ∀ X y : Fin n → ℝ, gmBox X y →
      |gmIt p c c' (N + 1) y - gmIt p c c' N y| ≤ q ^ N * ∑ j, X j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro N
  induction N with
  | zero =>
    intro X y hy
    have h0 : gmIt p c c' 0 y = ⨆ _i : Fin n, (0:ℝ) := by simp [gmIt]
    show |(⨆ i, mineOption p c c' (gmIt p c c' 0) y i) - gmIt p c c' 0 y| ≤ q ^ 0 * ∑ j, X j
    rw [h0, pow_zero, one_mul]
    apply gm_sup_diff
    intro i
    rw [gm_opt_split]
    simp only [gmIt, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
    have hs0 : 0 ≤ ∑ k, p i k * c i k := Finset.sum_nonneg fun k _ => mul_nonneg (hp i k) (hc0 i k)
    have hs1 : ∑ k, p i k * c i k ≤ 1 := by
      calc ∑ k, p i k * c i k ≤ ∑ k, p i k := Finset.sum_le_sum fun k _ => by
            nlinarith [hp i k, hc1 i k]
        _ ≤ 1 := by linarith [hq i]
    have hyi : y i ≤ ∑ j, X j := by
      calc y i ≤ ∑ j, y j := Finset.single_le_sum (fun j _ => (hy j).1) (Finset.mem_univ i)
        _ ≤ ∑ j, X j := Finset.sum_le_sum fun j _ => (hy j).2
    rw [abs_of_nonneg (mul_nonneg hs0 (hy i).1)]
    nlinarith [(hy i).1]
  | succ N ih =>
    intro X y hy
    show |(⨆ i, mineOption p c c' (gmIt p c c' (N + 1)) y i) -
      (⨆ i, mineOption p c c' (gmIt p c c' N) y i)| ≤ q ^ (N + 1) * ∑ j, X j
    apply gm_sup_diff
    intro i
    have hW : 0 ≤ ∑ j, X j := Finset.sum_nonneg fun j _ => (hy j).1.trans (hy j).2
    have := gm_opt_diff p c c' hp (gmIt p c c' (N + 1)) (gmIt p c c' N) y i q (q ^ N * ∑ j, X j)
      (hq i) (mul_nonneg (pow_nonneg hq0 _) hW)
      (fun k => ih X _ (gm_upd_box c c' hc0 hc1 hc' X y hy i k))
    calc _ ≤ q * (q ^ N * ∑ j, X j) := this
      _ = _ := by ring


include hp hc0 hc1 hc' in
lemma gm_dec_upd (hps : ∀ i, ∑ k, p i k < 1) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (i j : Fin n)
    (hij : j ≠ i) (k : Fin K) (hmax : ∀ m, decisionFunction p c x m ≤ decisionFunction p c x i) :
    ∀ m, decisionFunction p c (Function.update x j (c' j k * x j)) m ≤
      decisionFunction p c (Function.update x j (c' j k * x j)) i := by
  intro m
  unfold decisionFunction
  rw [Function.update_of_ne (Ne.symm hij)]
  by_cases hm : m = j
  · subst hm
    rw [Function.update_self]
    have h1 := hmax m
    unfold decisionFunction at h1
    refine le_trans ?_ h1
    apply div_le_div_of_nonneg_right _ (by linarith [hps m])
    apply mul_le_mul_of_nonneg_left (gm_upd_le c c' hc0 hc' x hx m k m |>.trans_eq' (by simp))
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hp m k) (hc0 m k)
  · rw [Function.update_of_ne hm]
    have h1 := hmax m
    unfold decisionFunction at h1
    exact h1

lemma gm_opt_succ_ge (N : ℕ) (x : Fin n → ℝ) (i j : Fin n) (hp' : ∀ i k, 0 ≤ p i k) (hij : j ≠ i) :
    ∑ l, p i l * (c i l * x i + ∑ k, p j k * (c j k * x j +
      gmIt p c c' N (Function.update (Function.update x i (c' i l * x i)) j (c' j k * x j)))) ≤
    mineOption p c c' (gmIt p c c' (N + 1)) x i := by
  unfold mineOption
  refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hp' i l)
  have := gm_it_ge p c c' N (Function.update x i (c' i l * x i)) j
  unfold mineOption at this
  rw [Function.update_of_ne hij] at this
  linarith

include hp hc0 hc1 hc' in
lemma gm_idx (hn : 0 < n) (hps : ∀ i, ∑ k, p i k < 1) (q : ℝ) (hq : ∀ i, ∑ k, p i k ≤ q)
    (hq0 : 0 ≤ q) :
    ∀ N : ℕ, ∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) → ∀ i : Fin n,
      (∀ m, decisionFunction p c x m ≤ decisionFunction p c x i) → ∀ j : Fin n,
      mineOption p c c' (gmIt p c c' N) x j ≤ mineOption p c c' (gmIt p c c' N) x i +
        q ^ N * ∑ m, x m := by
  intro N
  induction N with
  | zero =>
    intro x hx i hi j
    rw [gm_opt_split, gm_opt_split]
    simp only [gmIt, mul_zero, Finset.sum_const_zero, add_zero, pow_zero, one_mul]
    have hs0 : 0 ≤ ∑ k, p i k * c i k := Finset.sum_nonneg fun k _ => mul_nonneg (hp i k) (hc0 i k)
    have hs1 : ∑ k, p j k * c j k ≤ 1 := by
      calc ∑ k, p j k * c j k ≤ ∑ k, p j k := Finset.sum_le_sum fun k _ => by
            nlinarith [hp j k, hc1 j k]
        _ ≤ 1 := by linarith [hps j]
    have hxj : x j ≤ ∑ m, x m := Finset.single_le_sum (fun m _ => hx m) (Finset.mem_univ j)
    nlinarith [hx j, hx i, mul_nonneg hs0 (hx i)]
  | succ N ih =>
    intro x hx i hi j
    by_cases hij : j = i
    · subst hij
      have : 0 ≤ q ^ (N + 1) * ∑ m, x m :=
        mul_nonneg (pow_nonneg hq0 _) (Finset.sum_nonneg fun m _ => hx m)
      linarith
    have hge := gm_opt_succ_ge p c c' N x i j hp hij
    -- upper bound for option j
    have hup : mineOption p c c' (gmIt p c c' (N + 1)) x j ≤
        ∑ k, p j k * (c j k * x j + (∑ l, p i l * (c i l * x i +
          gmIt p c c' N (Function.update (Function.update x j (c' j k * x j)) i (c' i l * x i)))
          + q ^ N * ∑ m, x m)) := by
      unfold mineOption
      refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hp j k)
      set y := Function.update x j (c' j k * x j) with hy
      have hy0 : ∀ m, 0 ≤ y m := gm_upd_nonneg c c' hc1 hc' x hx j k
      obtain ⟨m, hm⟩ := gm_it_eq p c c' hn N y
      have h1 := ih y hy0 i (gm_dec_upd p c c' hp hc0 hc1 hc' hps x hx i j hij k hi) m
      have hW := gm_W_upd c c' hc0 hc' x hx j k
      rw [← hy] at hW
      have hyi : y i = x i := by rw [hy, Function.update_of_ne (Ne.symm hij)]
      have h2 : mineOption p c c' (gmIt p c c' N) y i = ∑ l, p i l * (c i l * x i +
          gmIt p c c' N (Function.update y i (c' i l * x i))) := by
        unfold mineOption; rw [hyi]
      have h3 : q ^ N * ∑ m, y m ≤ q ^ N * ∑ m, x m :=
        mul_le_mul_of_nonneg_left hW (pow_nonneg hq0 _)
      rw [hm]; linarith
    have hcomm : ∀ k l, Function.update (Function.update x j (c' j k * x j)) i (c' i l * x i) =
        Function.update (Function.update x i (c' i l * x i)) j (c' j k * x j) :=
      fun k l => Function.update_comm hij _ _ _
    simp only [hcomm] at hup
    have e1 := gm_alg1 (p j) (p i) (c j) (c i) (x j) (x i) (q ^ N * ∑ m, x m)
      (fun k l => gmIt p c c' N (Function.update (Function.update x i (c' i l * x i)) j (c' j k * x j)))
    have e2 := gm_alg2 (p j) (p i) (c j) (c i) (x j) (x i)
      (fun k l => gmIt p c c' N (Function.update (Function.update x i (c' i l * x i)) j (c' j k * x j)))
    have hup' := hup.trans_eq e1
    have hge' := hge
    rw [e2] at hge'
    -- index inequality
    have hD := hi j
    unfold decisionFunction at hD
    have hPi : 0 < 1 - ∑ k, p i k := by linarith [hps i]
    have hPj : 0 < 1 - ∑ k, p j k := by linarith [hps j]
    rw [div_le_div_iff₀ hPj hPi] at hD
    have hW0 : 0 ≤ q ^ N * ∑ m, x m := mul_nonneg (pow_nonneg hq0 _) (Finset.sum_nonneg fun m _ => hx m)
    have hPq : (∑ k, p j k) * (q ^ N * ∑ m, x m) ≤ q * (q ^ N * ∑ m, x m) :=
      mul_le_mul_of_nonneg_right (hq j) hW0
    have hpow : q ^ (N + 1) * ∑ m, x m = q * (q ^ N * ∑ m, x m) := by ring
    rw [hpow]
    nlinarith

noncomputable def gmLim (y : Fin n → ℝ) : ℝ := limUnder atTop (fun N => gmIt p c c' N y)

include hp hc0 hc1 hc' in
lemma gm_err (hn : 0 < n) (q : ℝ) (hq : ∀ i, ∑ k, p i k ≤ q) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (X y : Fin n → ℝ) (hy : gmBox X y) (N : ℕ) :
    |gmIt p c c' N y - gmLim p c c' y| ≤ (∑ j, X j) / (1 - q) * q ^ N := by
  have hu : ∀ N, dist (gmIt p c c' N y) (gmIt p c c' (N + 1) y) ≤ (∑ j, X j) * q ^ N := by
    intro N
    rw [Real.dist_eq, abs_sub_comm, mul_comm]
    exact gm_cauchy p c c' hp hc0 hc1 hc' hn q hq hq0 hq1 N X y hy
  have hcs := cauchySeq_of_le_geometric q (∑ j, X j) hq1 hu
  have ht := hcs.tendsto_limUnder
  have := dist_le_of_le_geometric_of_tendsto q (∑ j, X j) hq1 hu ht N
  rw [Real.dist_eq] at this
  rw [div_mul_eq_mul_div]
  exact this

lemma gm_box_self (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) : gmBox x x := fun j => ⟨hx j, le_rfl⟩

include hp hc0 hc1 hc' in
lemma gm_lim_idx (hn : 0 < n) (hps : ∀ i, ∑ k, p i k < 1) (q : ℝ) (hq : ∀ i, ∑ k, p i k ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (i : Fin n)
    (hi : ∀ m, decisionFunction p c x m ≤ decisionFunction p c x i) :
    (∀ j, mineOption p c c' (gmLim p c c') x j ≤ mineOption p c c' (gmLim p c c') x i) ∧
      gmLim p c c' x = mineOption p c c' (gmLim p c c') x i := by
  set W := ∑ j, x j with hWdef
  have hW : 0 ≤ W := Finset.sum_nonneg fun j _ => hx j
  set E := W / (1 - q) with hE
  have hE0 : 0 ≤ E := div_nonneg hW (by linarith)
  have hqN : ∀ N : ℕ, 0 ≤ q ^ N := fun N => pow_nonneg hq0 N
  -- option error
  have hopt : ∀ N j, |mineOption p c c' (gmLim p c c') x j - mineOption p c c' (gmIt p c c' N) x j|
      ≤ q * (E * q ^ N) := by
    intro N j
    apply gm_opt_diff p c c' hp _ _ x j q _ (hq j) (mul_nonneg hE0 (hqN N))
    intro k
    rw [abs_sub_comm]
    exact gm_err p c c' hp hc0 hc1 hc' hn q hq hq0 hq1 x _
      (gm_upd_box c c' hc0 hc1 hc' x x (gm_box_self x hx) j k) N
  have herr : ∀ N, |gmIt p c c' N x - gmLim p c c' x| ≤ E * q ^ N :=
    gm_err p c c' hp hc0 hc1 hc' hn q hq hq0 hq1 x x (gm_box_self x hx)
  have hidx := gm_idx p c c' hp hc0 hc1 hc' hn hps q hq hq0
  have hpow : ∀ N : ℕ, q ^ (N + 1) = q ^ N * q := fun N => pow_succ q N
  refine ⟨fun j => ?_, le_antisymm ?_ ?_⟩
  · apply gm_geo_le hq0 hq1 (C := 2 * q * E + W)
    intro N
    have h1 := (abs_sub_le_iff.1 (hopt N j)).1
    have h2 := (abs_sub_le_iff.1 (hopt N i)).2
    have h3 := hidx N x hx i hi j
    nlinarith
  · apply gm_geo_le hq0 hq1 (C := 2 * q * E + W)
    intro N
    obtain ⟨m, hm⟩ := gm_it_eq p c c' hn N x
    have h1 := (abs_sub_le_iff.1 (herr (N + 1))).2
    have h2 := (abs_sub_le_iff.1 (hopt N i)).2
    have h3 := hidx N x hx i hi m
    rw [hpow] at h1
    nlinarith
  · apply gm_geo_le hq0 hq1 (C := 2 * q * E)
    intro N
    have h1 := (abs_sub_le_iff.1 (herr (N + 1))).1
    have h2 := (abs_sub_le_iff.1 (hopt N i)).1
    have h3 := gm_it_ge p c c' N x i
    rw [hpow] at h1
    nlinarith

include hp hc0 hc1 hc' in
lemma gm_unique (hn : 0 < n) (q : ℝ) (hq : ∀ i, ∑ k, p i k ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (g : (Fin n → ℝ) → ℝ) (hg : IsNMineSolution p c c' g)
    (hgb : BoundedOnBoxes g) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    g x = gmLim p c c' x := by
  obtain ⟨M, hM⟩ := hgb x
  have hM' : ∀ y, gmBox x y → |g y| ≤ M := fun y hy => hM y hy
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' x (gm_box_self x hx))
  have hqN : ∀ N : ℕ, 0 ≤ q ^ N := fun N => pow_nonneg hq0 N
  have claim : ∀ N : ℕ, ∀ y, gmBox x y → |g y - gmIt p c c' N y| ≤ q ^ N * M := by
    intro N
    induction N with
    | zero => intro y hy; simpa [gmIt] using hM' y hy
    | succ N ih =>
      intro y hy
      have hy0 : ∀ j, 0 ≤ y j := fun j => (hy j).1
      have hopt : ∀ m, |mineOption p c c' g y m - mineOption p c c' (gmIt p c c' N) y m|
          ≤ q * (q ^ N * M) := fun m =>
        gm_opt_diff p c c' hp _ _ y m q _ (hq m) (mul_nonneg (hqN N) hM0)
          (fun k => ih _ (gm_upd_box c c' hc0 hc1 hc' x y hy m k))
      obtain ⟨hall, i0, hi0⟩ := hg y hy0
      obtain ⟨m, hm⟩ := gm_it_eq p c c' hn N y
      have h1 := (abs_sub_le_iff.1 (hopt i0)).1
      have h2 := (abs_sub_le_iff.1 (hopt m)).2
      have h3 := gm_it_ge p c c' N y i0
      have h4 := hall m
      rw [pow_succ, abs_sub_le_iff]
      constructor <;> nlinarith
  set W := ∑ j, x j
  have hW : 0 ≤ W := Finset.sum_nonneg fun j _ => hx j
  have herr := gm_err p c c' hp hc0 hc1 hc' hn q hq hq0 hq1 x x (gm_box_self x hx)
  apply le_antisymm
  · apply gm_geo_le hq0 hq1 (C := M + W / (1 - q))
    intro N
    have h1 := (abs_sub_le_iff.1 (claim N x (gm_box_self x hx))).1
    have h2 := (abs_sub_le_iff.1 (herr N)).1
    nlinarith
  · apply gm_geo_le hq0 hq1 (C := M + W / (1 - q))
    intro N
    have h1 := (abs_sub_le_iff.1 (claim N x (gm_box_self x hx))).2
    have h2 := (abs_sub_le_iff.1 (herr N)).2
    nlinarith

include hp hc0 hc1 hc' in
theorem gm_main (hn : 0 < n) (hps : ∀ i, ∑ k, p i k < 1) :
    ∃ f : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' f ∧ BoundedOnBoxes f ∧
      (∀ g : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' g → BoundedOnBoxes g →
        ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → g x = f x) ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∀ i : Fin n,
        (∀ j : Fin n, decisionFunction p c x j ≤ decisionFunction p c x i) →
          f x = mineOption p c c' f x i := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ∑ k, p i k)
  set q := ∑ k, p i0 k
  have hq : ∀ i, ∑ k, p i k ≤ q := hi0
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun k _ => hp i0 k
  have hq1 : q < 1 := hps i0
  have hidx := gm_lim_idx p c c' hp hc0 hc1 hc' hn hps q hq hq0 hq1
  refine ⟨gmLim p c c', ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Finite.exists_max (fun i => decisionFunction p c x i)
    obtain ⟨h1, h2⟩ := hidx x hx i hi
    exact ⟨fun j => (h1 j).trans h2.symm.le, i, h2⟩
  · intro X
    refine ⟨(∑ j, X j) / (1 - q) * q ^ 0, fun y hy => ?_⟩
    have := gm_err p c c' hp hc0 hc1 hc' hn q hq hq0 hq1 X y hy 0
    simpa [gmIt] using this
  · exact fun g hg hgb x hx => gm_unique p c c' hp hc0 hc1 hc' hn q hq hq0 hq1 g hg hgb x hx
  · exact fun x hx i hi => (hidx x hx i hi).2

include hp hc0 hc1 hc' in
theorem gm_index_any (hn : 0 < n) (hps : ∀ i, ∑ k, p i k < 1)
    (g : (Fin n → ℝ) → ℝ) (hg : IsNMineSolution p c c' g) (hgb : BoundedOnBoxes g)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (i : Fin n)
    (hi : ∀ j : Fin n, decisionFunction p c x j ≤ decisionFunction p c x i) :
    g x = mineOption p c c' g x i := by
  obtain ⟨f, _, _, hu, hidx⟩ := gm_main p c c' hp hc0 hc1 hc' hn hps
  rw [hu g hg hgb x hx, hidx x hx i hi]
  unfold mineOption
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hu g hg hgb _ (gm_upd_nonneg c c' hc1 hc' x hx i k)]

end Core


end BellmanDP.GoldMining

open BellmanDP.GoldMining


theorem solution (n K : ℕ) (hn : 0 < n) (p c c' : Fin n → Fin K → ℝ)
    (hp : ∀ i k, 0 ≤ p i k) (hps : ∀ i, ∑ k, p i k < 1)
    (hc0 : ∀ i k, 0 ≤ c i k) (hc1 : ∀ i k, c i k ≤ 1) (hc' : ∀ i k, c i k + c' i k = 1) :
    ∃ f : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' f ∧ BoundedOnBoxes f ∧
      (∀ g : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' g → BoundedOnBoxes g →
        ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → g x = f x) ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∀ i : Fin n,
        (∀ j : Fin n, decisionFunction p c x j ≤ decisionFunction p c x i) →
          f x = mineOption p c c' f x i := by
  exact gm_main p c c' hp hc0 hc1 hc' hn hps
