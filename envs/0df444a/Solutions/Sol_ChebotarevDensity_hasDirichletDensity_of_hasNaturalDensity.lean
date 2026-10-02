-- Prove2me | solution 1 for ChebotarevDensity.hasDirichletDensity_of_hasNaturalDensity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:42:29.380915+00:00
-- url     : https://prove2.me/submissions/a96c04d0-03d0-4dae-80f8-01f1f222f37f

import Theorems.Thm_ChebotarevDensity_hasDirichletDensity_primes

open Polynomial NumberField
open ChebotarevDensity
open scoped Classical

/-- Abel summation, finite form. -/
private lemma abel_fin (c g : ℕ → ℝ) (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), c k * g k =
      (∑ k ∈ Finset.range (M + 1), c k) * g M +
      ∑ n ∈ Finset.range M, (∑ k ∈ Finset.range (n + 1), c k) * (g n - g (n + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h1 := Finset.sum_range_succ (fun k => c k * g k) (M + 1)
    have h2 := Finset.sum_range_succ c (M + 1)
    have h3 := Finset.sum_range_succ
      (fun n => (∑ k ∈ Finset.range (n + 1), c k) * (g n - g (n + 1))) M
    rw [h1, ih, h2, h3]
    ring

private lemma abel_bound (c b g : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hg : Antitone g) (hg0 : ∀ k, 0 ≤ g k) (hg1 : g 0 ≤ 1)
    (ε K Q : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hC : ∀ n, |∑ k ∈ Finset.range (n + 1), c k| ≤ ε * ∑ k ∈ Finset.range (n + 1), b k + K)
    (hQ : ∀ M, ∑ k ∈ Finset.range (M + 1), b k * g k ≤ Q) (M : ℕ) :
    |∑ k ∈ Finset.range (M + 1), c k * g k| ≤ 2 * ε * Q + 2 * K := by
  have hBpos : ∀ n, 0 ≤ ∑ k ∈ Finset.range (n + 1), b k :=
    fun n => Finset.sum_nonneg (fun k _ => hb k)
  have hd : ∀ n, 0 ≤ g n - g (n + 1) := fun n => sub_nonneg.mpr (hg (Nat.le_succ n))
  have hBg : (∑ k ∈ Finset.range (M + 1), b k) * g M ≤ ∑ k ∈ Finset.range (M + 1), b k * g k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    exact mul_le_mul_of_nonneg_left (hg (by simpa [Nat.lt_succ_iff] using hk)) (hb k)
  have hab := abel_fin b g M
  have hBsum : ∑ n ∈ Finset.range M, (∑ k ∈ Finset.range (n + 1), b k) * (g n - g (n + 1)) ≤ Q := by
    have : 0 ≤ (∑ k ∈ Finset.range (M + 1), b k) * g M := mul_nonneg (hBpos M) (hg0 M)
    linarith [hQ M]
  have htel : ∑ n ∈ Finset.range M, (g n - g (n + 1)) ≤ 1 := by
    rw [Finset.sum_range_sub']
    linarith [hg0 M]
  have hlast : |∑ k ∈ Finset.range (M + 1), c k| * g M ≤ ε * Q + K := by
    calc |∑ k ∈ Finset.range (M + 1), c k| * g M
        ≤ (ε * ∑ k ∈ Finset.range (M + 1), b k + K) * g M :=
          mul_le_mul_of_nonneg_right (hC M) (hg0 M)
      _ = ε * ((∑ k ∈ Finset.range (M + 1), b k) * g M) + K * g M := by ring
      _ ≤ ε * Q + K * 1 := by
          have h1 : g M ≤ 1 := (hg (Nat.zero_le M)).trans hg1
          have := mul_le_mul_of_nonneg_left (hBg.trans (hQ M)) hε
          nlinarith [mul_le_mul_of_nonneg_left h1 hK]
      _ = ε * Q + K := by ring
  have hmid : |∑ n ∈ Finset.range M, (∑ k ∈ Finset.range (n + 1), c k) * (g n - g (n + 1))|
      ≤ ε * Q + K := by
    calc _ ≤ ∑ n ∈ Finset.range M, |(∑ k ∈ Finset.range (n + 1), c k) * (g n - g (n + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range M, ((ε * ∑ k ∈ Finset.range (n + 1), b k + K) * (g n - g (n + 1))) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          rw [abs_mul, abs_of_nonneg (hd n)]
          exact mul_le_mul_of_nonneg_right (hC n) (hd n)
      _ = ε * ∑ n ∈ Finset.range M, (∑ k ∈ Finset.range (n + 1), b k) * (g n - g (n + 1))
            + K * ∑ n ∈ Finset.range M, (g n - g (n + 1)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          ring
      _ ≤ ε * Q + K * 1 := by
          have := mul_le_mul_of_nonneg_left hBsum hε
          have := mul_le_mul_of_nonneg_left htel hK
          linarith
      _ = ε * Q + K := by ring
  rw [abel_fin]
  calc _ ≤ |(∑ k ∈ Finset.range (M + 1), c k) * g M| +
        |∑ n ∈ Finset.range M, (∑ k ∈ Finset.range (n + 1), c k) * (g n - g (n + 1))| :=
        abs_add_le _ _
    _ ≤ (ε * Q + K) + (ε * Q + K) := by
        rw [abs_mul, abs_of_nonneg (hg0 M)]
        exact add_le_add hlast hmid
    _ = 2 * ε * Q + 2 * K := by ring

private noncomputable def gf (s : ℝ) (n : ℕ) : ℝ := ((max n 1 : ℕ) : ℝ) ^ (-s)

private noncomputable def ind (T : Set ℕ) (n : ℕ) : ℝ := if n ∈ T then 1 else 0

private lemma ind_nonneg (T : Set ℕ) (n : ℕ) : 0 ≤ ind T n := by
  unfold ind; split_ifs <;> norm_num

private lemma gf_nonneg (s : ℝ) (n : ℕ) : 0 ≤ gf s n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private lemma gf_antitone {s : ℝ} (hs : 0 ≤ s) : Antitone (gf s) := by
  intro n m hnm
  unfold gf
  refine Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (lt_of_lt_of_le one_pos (le_max_right n 1)))
    (by exact_mod_cast max_le_max hnm le_rfl) (by linarith)

private lemma gf_zero (s : ℝ) : gf s 0 = 1 := by simp [gf]

private lemma gf_of_prime (s : ℝ) {n : ℕ} (hn : n.Prime) : gf s n = (n : ℝ) ^ (-s) := by
  unfold gf
  rw [max_eq_left hn.one_lt.le]

/-- The prime sum over `T ⊆ primes`, as a sum over `ℕ`. -/
private lemma tsum_sub (T : Set ℕ) (hT : ∀ n ∈ T, n.Prime) (s : ℝ) :
    ∑' p : {p : ℕ // p.Prime ∧ p ∈ T}, ((p : ℕ) : ℝ) ^ (-s) = ∑' n : ℕ, ind T n * gf s n := by
  have e : ∑' p : {p : ℕ // p.Prime ∧ p ∈ T}, ((p : ℕ) : ℝ) ^ (-s)
      = ∑' p : T, ((p : ℕ) : ℝ) ^ (-s) :=
    (Equiv.subtypeEquivRight (fun p => ⟨fun h => h.2, fun h => ⟨hT p h, h⟩⟩) :
      {p : ℕ // p.Prime ∧ p ∈ T} ≃ T).tsum_eq (fun p : T => ((p : ℕ) : ℝ) ^ (-s))
  rw [e, tsum_subtype T (fun n : ℕ => (n : ℝ) ^ (-s))]
  refine tsum_congr (fun n => ?_)
  by_cases hn : n ∈ T
  · simp [Set.indicator, ind, hn, gf_of_prime s (hT n hn)]
  · simp [Set.indicator, ind, hn]

private lemma summable_ind_primes {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ind {n | n.Prime} n * gf s n) := by
  have h1 : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have h2 : Summable (Set.indicator {n : ℕ | n.Prime} (fun n : ℕ => (n : ℝ) ^ (-s))) :=
    (summable_subtype_iff_indicator (s := {n : ℕ | n.Prime})).mp h1
  refine h2.congr (fun n => ?_)
  by_cases hn : n.Prime
  · simp [Set.indicator, ind, hn, gf_of_prime s hn]
  · simp [Set.indicator, ind, hn]

private lemma summable_ind_sub {s : ℝ} (hs : 1 < s) (T : Set ℕ) (hT : ∀ n ∈ T, n.Prime) :
    Summable (fun n : ℕ => ind T n * gf s n) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ind_nonneg _ _) (gf_nonneg _ _))
    (fun n => ?_) (summable_ind_primes hs)
  refine mul_le_mul_of_nonneg_right ?_ (gf_nonneg _ _)
  unfold ind
  by_cases hn : n ∈ T
  · simp [hn, hT n hn]
  · simp only [hn, if_false]
    split_ifs <;> norm_num

private lemma sum_ind (T : Set ℕ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ind T k = (((Finset.Iic n).filter (fun p => p ∈ T)).card : ℝ) := by
  rw [Nat.range_succ_eq_Iic, Finset.natCast_card_filter]
  rfl

private lemma eventually_bound (S : Set ℕ) (δ : ℝ) (h : HasNaturalDensity S δ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ n ≥ N0,
      |∑ k ∈ Finset.range (n + 1), (ind {n | n.Prime ∧ n ∈ S} k - δ * ind {n | n.Prime} k)|
        ≤ ε * ∑ k ∈ Finset.range (n + 1), ind {n | n.Prime} k := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε
  refine ⟨max N 2, fun n hn => ?_⟩
  have hn1 : N ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hd := hN n hn1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ind, sum_ind]
  simp only [Set.mem_ofPred_eq]
  set A : ℝ := (((Finset.Iic n).filter (fun p => p.Prime ∧ p ∈ S)).card : ℝ) with hA
  set Pn : ℝ := (((Finset.Iic n).filter (fun p => p.Prime)).card : ℝ) with hPn
  have hPpos : 0 < Pn := by
    rw [hPn]
    exact_mod_cast Finset.card_pos.mpr ⟨2, by simp [hn2, Nat.prime_two]⟩
  rw [Real.dist_eq] at hd
  have : A - δ * Pn = (A / Pn - δ) * Pn := by field_simp
  rw [this, abs_mul, abs_of_pos hPpos]
  exact mul_le_mul_of_nonneg_right hd.le hPpos.le

private lemma key_estimate (S : Set ℕ) (δ : ℝ) (h : HasNaturalDensity S δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 1 < s →
      |∑' n : ℕ, ind {n | n.Prime ∧ n ∈ S} n * gf s n - δ * ∑' n : ℕ, ind {n | n.Prime} n * gf s n|
        ≤ 2 * ε * ∑' n : ℕ, ind {n | n.Prime} n * gf s n + 2 * K := by
  obtain ⟨N0, hN0⟩ := eventually_bound S δ h hε
  refine ⟨∑ n ∈ Finset.range N0, |∑ k ∈ Finset.range (n + 1),
    (ind {n | n.Prime ∧ n ∈ S} k - δ * ind {n | n.Prime} k)|,
    Finset.sum_nonneg (fun n _ => abs_nonneg _), fun s hs => ?_⟩
  set K := ∑ n ∈ Finset.range N0, |∑ k ∈ Finset.range (n + 1),
    (ind {n | n.Prime ∧ n ∈ S} k - δ * ind {n | n.Prime} k)| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun n _ => abs_nonneg _)
  have hsA := summable_ind_sub hs {n | n.Prime ∧ n ∈ S} (fun n hn => hn.1)
  have hsP := summable_ind_primes hs
  have hbound : ∀ M, |∑ k ∈ Finset.range (M + 1),
      (ind {n | n.Prime ∧ n ∈ S} k - δ * ind {n | n.Prime} k) * gf s k|
      ≤ 2 * ε * ∑' n : ℕ, ind {n | n.Prime} n * gf s n + 2 * K := by
    intro M
    refine abel_bound _ (ind {n | n.Prime}) (gf s) (fun k => ind_nonneg _ _)
      (gf_antitone (by linarith)) (gf_nonneg s) (gf_zero s).le ε K _ hε.le hK0 ?_ ?_ M
    · intro n
      by_cases hn : N0 ≤ n
      · have := hN0 n hn
        have h0 : 0 ≤ ε * ∑ k ∈ Finset.range (n + 1), ind {n | n.Prime} k :=
          mul_nonneg hε.le (Finset.sum_nonneg (fun k _ => ind_nonneg _ _))
        linarith
      · have hlt : n < N0 := not_le.mp hn
        have : |∑ k ∈ Finset.range (n + 1),
            (ind {n | n.Prime ∧ n ∈ S} k - δ * ind {n | n.Prime} k)| ≤ K :=
          Finset.single_le_sum (f := fun n => |∑ k ∈ Finset.range (n + 1),
            (ind {n | n.Prime ∧ n ∈ S} k - δ * ind {n | n.Prime} k)|)
            (fun n _ => abs_nonneg _) (Finset.mem_range.mpr hlt)
        have h0 : 0 ≤ ε * ∑ k ∈ Finset.range (n + 1), ind {n | n.Prime} k :=
          mul_nonneg hε.le (Finset.sum_nonneg (fun k _ => ind_nonneg _ _))
        linarith
    · intro M
      exact hsP.sum_le_tsum _ (fun k _ => mul_nonneg (ind_nonneg _ _) (gf_nonneg _ _))
  have hHas : HasSum (fun n : ℕ => (ind {n | n.Prime ∧ n ∈ S} n - δ * ind {n | n.Prime} n) * gf s n)
      (∑' n : ℕ, ind {n | n.Prime ∧ n ∈ S} n * gf s n - δ * ∑' n : ℕ, ind {n | n.Prime} n * gf s n) := by
    have := hsA.hasSum.sub (hsP.hasSum.mul_left δ)
    have e : (fun n : ℕ => (ind {n | n.Prime ∧ n ∈ S} n - δ * ind {n | n.Prime} n) * gf s n)
        = (fun b : ℕ => ind {n | n.Prime ∧ n ∈ S} b * gf s b
            - δ * (ind {n | n.Prime} b * gf s b)) := by
      funext n
      ring
    rw [e]
    exact this
  have ht := (Filter.tendsto_add_atTop_iff_nat 1).mpr hHas.tendsto_sum_nat
  exact le_of_tendsto' ht.abs hbound

private lemma final_ineq (A P L δ K ε e : ℝ) (hL : 0 < L) (hP0 : 0 ≤ P) (hε : ε = e / 9)
    (he : 0 < e)
    (hk : |A - δ * P| ≤ 2 * ε * P + 2 * K) (h1 : |P / L - 1| < 1 / 2)
    (h2 : |δ| * |P / L - 1| < e / 3) (h3 : 2 * K / L < e / 3) : |A / L - δ| < e := by
  have e1 : A / L - δ = (A - δ * P) / L + δ * (P / L - 1) := by field_simp; ring
  have hq : P / L < 3 / 2 := by
    have := (abs_lt.mp h1).2
    linarith
  have e2 : |(A - δ * P) / L| ≤ 2 * ε * (P / L) + 2 * K / L := by
    rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
    have : (2 * ε * (P / L) + 2 * K / L) * L = 2 * ε * P + 2 * K := by field_simp
    rw [this]; exact hk
  have hpl : 0 ≤ P / L := div_nonneg hP0 hL.le
  have e3 : 2 * ε * (P / L) ≤ e / 3 := by
    rw [hε]; nlinarith
  rw [e1]
  calc |(A - δ * P) / L + δ * (P / L - 1)|
      ≤ |(A - δ * P) / L| + |δ * (P / L - 1)| := abs_add_le _ _
    _ < e := by
        rw [abs_mul]
        linarith

private lemma tendsto_L :
    Filter.Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1))
      Filter.atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h : Filter.Tendsto (fun s : ℝ => s - 1) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Filter.Tendsto (fun s : ℝ => s - 1) (nhds 1) (nhds (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  simpa [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp h

private lemma tsum_sub' (S : Set ℕ) (s : ℝ) :
    ∑' p : {p : ℕ // p.Prime ∧ p ∈ S}, ((p : ℕ) : ℝ) ^ (-s)
      = ∑' n : ℕ, ind {n | n.Prime ∧ n ∈ S} n * gf s n := by
  rw [← tsum_sub {n | n.Prime ∧ n ∈ S} (fun n hn => hn.1) s]
  exact (Equiv.subtypeEquivRight (fun p => by simp) :
    {p : ℕ // p.Prime ∧ p ∈ S} ≃ {p : ℕ // p.Prime ∧ p ∈ {n | n.Prime ∧ n ∈ S}}).tsum_eq
      (fun p : {p : ℕ // p.Prime ∧ p ∈ {n | n.Prime ∧ n ∈ S}} => ((p : ℕ) : ℝ) ^ (-s))

theorem solution (S : Set ℕ) (δ : ℝ)
    (h : HasNaturalDensity S δ) : HasDirichletDensity S δ := by
  have hP := hasDirichletDensity_primes
  unfold HasDirichletDensity at hP ⊢
  have hPe : ∀ s : ℝ, ∑' p : {p : ℕ // p.Prime ∧ p ∈ {p : ℕ | p.Prime}}, ((p : ℕ) : ℝ) ^ (-s)
      = ∑' n : ℕ, ind {n | n.Prime} n * gf s n := fun s =>
    tsum_sub {n | n.Prime} (fun n hn => hn) s
  simp_rw [hPe] at hP
  simp_rw [tsum_sub']
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨K, hK0, hKb⟩ := key_estimate S δ h (ε := e / 9) (by positivity)
  have hc : (0 : ℝ) < e / (3 * (|δ| + 1)) := by positivity
  have hP1 := (Metric.tendsto_nhds.mp hP) (min (1 / 2) (e / (3 * (|δ| + 1))))
    (lt_min (by norm_num) hc)
  have hK3 : Filter.Tendsto (fun s : ℝ => 2 * K / Real.log (1 / (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_L
  have hK4 := hK3.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < e / 3))
  filter_upwards [self_mem_nhdsWithin, tendsto_L.eventually_gt_atTop 0, hP1, hK4]
    with s hs hL hPs hKs
  have hs1 : 1 < s := hs
  rw [Real.dist_eq] at hPs ⊢
  have hP0 : 0 ≤ ∑' n : ℕ, ind {n | n.Prime} n * gf s n :=
    tsum_nonneg (fun n => mul_nonneg (ind_nonneg _ _) (gf_nonneg _ _))
  have hlt1 : |(∑' n : ℕ, ind {n | n.Prime} n * gf s n) / Real.log (1 / (s - 1)) - 1| < 1 / 2 :=
    lt_of_lt_of_le hPs (min_le_left _ _)
  have hlt2 : |(∑' n : ℕ, ind {n | n.Prime} n * gf s n) / Real.log (1 / (s - 1)) - 1|
      < e / (3 * (|δ| + 1)) := lt_of_lt_of_le hPs (min_le_right _ _)
  have h2 : |δ| * |(∑' n : ℕ, ind {n | n.Prime} n * gf s n) / Real.log (1 / (s - 1)) - 1|
      < e / 3 := by
    have hpos : (0 : ℝ) < |δ| + 1 := by positivity
    calc _ ≤ (|δ| + 1) * |(∑' n : ℕ, ind {n | n.Prime} n * gf s n) / Real.log (1 / (s - 1)) - 1| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (|δ| + 1) * (e / (3 * (|δ| + 1))) := mul_lt_mul_of_pos_left hlt2 hpos
      _ = e / 3 := by field_simp
  exact final_ineq _ _ _ δ K (e / 9) e hL hP0 rfl he (hKb s hs1) hlt1 h2 hKs
