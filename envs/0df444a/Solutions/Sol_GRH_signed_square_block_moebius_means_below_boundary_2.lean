-- Prove2me | solution 2 for GRH.signed_square_block_moebius_means_below_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T10:24:51.494575+00:00
-- url     : https://prove2.me/submissions/35d3b72b-999f-4f76-bfb3-ffada1881d02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GRH_MoebiusBilinear
import Theorems.Thm_GRH_reduced_liouville_harmonic_power_decay
import Theorems.Thm_GRH_reduced_moebius_harmonic_le_of_liouville_harmonic_le
import Theorems.Thm_GRH_moebius_square_block_partial_sum_mean
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators ArithmeticFunction
open Finset Nat ArithmeticFunction

namespace MoebiusCentered

variable {q : ℕ} [NeZero q]

def μR (n : ℕ) : ℝ := moebius n

/-- `∑_{d, e ≤ u, de ∣ n} μ(d) μ(e)`. -/
def pairSum (n u : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 u, ∑ e ∈ Ioc 0 u,
    if d * e ∣ n then μR d * μR e else 0

/-- Möbius sum over `0 ≤ k ≤ n` in the class `a`. The `k = 0` term vanishes. -/
def mertens (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), if (k : ZMod q) = a then μR k else 0

lemma div_ne_zero_of_dvd {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : n / d ≠ 0 := by
  intro h
  exact hn (by simpa [h] using (Nat.mul_div_cancel' hd).symm)

lemma sum_moebius_divisors_int (n : ℕ) :
    ∑ d ∈ n.divisors, moebius d = if n = 1 then (1 : ℤ) else 0 := by
  rw [← coe_mul_zeta_apply (f := moebius) (x := n), moebius_mul_coe_zeta]
  simp [one_apply]

lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, μR d = if n = 1 then (1 : ℝ) else 0 := by
  simpa [μR] using congrArg (Int.cast : ℤ → ℝ) (sum_moebius_divisors_int n)

lemma filter_Ioc_dvd_eq (m u : ℕ) (hm : m ≠ 0) :
    (Ioc 0 u).filter (· ∣ m) = m.divisors.filter (· ≤ u) := by
  ext d
  constructor
  · intro hd
    rcases mem_filter.mp hd with ⟨hdI, hdvd⟩
    rcases mem_Ioc.mp hdI with ⟨_, hdu⟩
    exact mem_filter.mpr ⟨mem_divisors.mpr ⟨hdvd, hm⟩, hdu⟩
  · intro hd
    rcases mem_filter.mp hd with ⟨hdmem, hdu⟩
    rcases mem_divisors.mp hdmem with ⟨hdvd, _⟩
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨pos_of_dvd_of_pos hdvd (pos_of_ne_zero hm), hdu⟩, hdvd⟩

lemma divisors_filter_le_of_le {n u : ℕ} (hn : n ≠ 0) (hnu : n ≤ u) :
    n.divisors.filter (· ≤ u) = n.divisors := by
  ext d
  constructor
  · exact fun hd => (mem_filter.mp hd).1
  · intro hd
    exact mem_filter.mpr ⟨hd,
      le_trans (le_of_dvd (pos_of_ne_zero hn) (dvd_of_mem_divisors hd)) hnu⟩

lemma pairSum_eq_divisors (n u : ℕ) (hn : n ≠ 0) :
    pairSum n u =
      ∑ d ∈ n.divisors.filter (· ≤ u),
        μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e := by
  unfold pairSum
  have hpull (d : ℕ) :
      ∑ e ∈ Ioc 0 u, (if d * e ∣ n then μR d * μR e else 0) =
        if d ∣ n then μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e else 0 := by
    by_cases hd : d ∣ n
    · rw [if_pos hd]
      have hmul (e : ℕ) : d * e ∣ n ↔ e ∣ n / d := by
        nth_rw 1 [← Nat.mul_div_cancel' hd]
        exact Nat.mul_dvd_mul_iff_left (pos_of_dvd_of_pos hd (pos_of_ne_zero hn))
      have hterm (e : ℕ) :
          (if d * e ∣ n then μR d * μR e else 0) =
            μR d * (if e ∣ n / d then μR e else 0) := by
        by_cases he : e ∣ n / d
        · rw [if_pos (hmul e |>.mpr he), if_pos he]
        · rw [if_neg (fun h => he ((hmul e).mp h)), if_neg he, mul_zero]
      simp_rw [hterm, ← mul_sum, ← sum_filter]
      rw [filter_Ioc_dvd_eq (n / d) u (div_ne_zero_of_dvd hn hd)]
    · rw [if_neg hd]
      refine sum_eq_zero fun e _ => ?_
      exact if_neg (fun h => hd (dvd_of_mul_right_dvd h))
  simp_rw [hpull, ← sum_filter]
  exact filter_Ioc_dvd_eq n u hn ▸ rfl

lemma pairSum_of_le {n u : ℕ} (hn : n ≠ 0) (hnu : n ≤ u) : pairSum n u = μR n := by
  rw [pairSum_eq_divisors n u hn, divisors_filter_le_of_le hn hnu]
  have hterm (d : ℕ) (hd : d ∈ n.divisors) :
      μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e =
        if d = n then μR n else 0 := by
    have hdvd := dvd_of_mem_divisors hd
    rw [divisors_filter_le_of_le (div_ne_zero_of_dvd hn hdvd)
      (le_trans (Nat.div_le_self n d) hnu), sum_moebius_divisors]
    by_cases h : d = n
    · rw [h, Nat.div_self (pos_of_ne_zero hn), if_pos rfl, if_pos rfl, mul_one]
    · have hne : n / d ≠ 1 := by
        intro heq
        have := Nat.mul_div_cancel' hdvd
        rw [heq, mul_one] at this
        exact h this
      rw [if_neg hne, if_neg h, mul_zero]
  exact (sum_congr rfl hterm).trans <| by
    rw [sum_ite_eq', if_pos (mem_divisors_self n hn)]

lemma fullSum_eq (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, μR d * ∑ e ∈ (n / d).divisors, μR e = μR n := by
  have hterm (d : ℕ) (hd : d ∈ n.divisors) :
      μR d * ∑ e ∈ (n / d).divisors, μR e = if d = n then μR n else 0 := by
    have hdvd := dvd_of_mem_divisors hd
    rw [sum_moebius_divisors]
    by_cases h : d = n
    · rw [h, Nat.div_self (pos_of_ne_zero hn), if_pos rfl, if_pos rfl, mul_one]
    · have hne : n / d ≠ 1 := by
        intro heq
        have := Nat.mul_div_cancel' hdvd
        rw [heq, mul_one] at this
        exact h this
      rw [if_neg hne, if_neg h, mul_zero]
  exact (sum_congr rfl hterm).trans <| by
    rw [sum_ite_eq', if_pos (mem_divisors_self n hn)]

lemma divisors_sum_split (m u : ℕ) (_hm : m ≠ 0) (f : ℕ → ℝ) :
    ∑ d ∈ m.divisors, f d =
      ∑ d ∈ m.divisors.filter (· ≤ u), f d +
        ∑ d ∈ m.divisors.filter (u < ·), f d := by
  have hdis : Disjoint (m.divisors.filter (· ≤ u)) (m.divisors.filter (u < ·)) := by
    rw [disjoint_filter]
    intro x _ hx1 hx2
    exact lt_irrefl _ (lt_of_le_of_lt hx1 hx2)
  have hun : m.divisors.filter (· ≤ u) ∪ m.divisors.filter (u < ·) = m.divisors := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_filter.mp hx).1
      · exact (mem_filter.mp hx).1
    · intro hx
      by_cases hle : x ≤ u
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hx, hle⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hx, lt_of_not_ge hle⟩))
  rw [← sum_union hdis, hun]

lemma mixed_swap (n u : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (u < ·),
        μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e =
      ∑ e ∈ n.divisors.filter (· ≤ u),
        μR e * ∑ d ∈ (n / e).divisors.filter (u < ·), μR d := by
  let s : Finset ℕ := n.divisors.filter (u < ·)
  let t : ℕ → Finset ℕ := fun d => (n / d).divisors.filter (· ≤ u)
  let s' : Finset ℕ := n.divisors.filter (· ≤ u)
  let t' : ℕ → Finset ℕ := fun e => (n / e).divisors.filter (u < ·)
  have hL :
      ∑ d ∈ s, μR d * ∑ e ∈ t d, μR e =
        ∑ p ∈ s.sigma t, μR p.1 * μR p.2 := by
    simp [s, t, sum_sigma, mul_sum]
  have hR :
      ∑ e ∈ s', μR e * ∑ d ∈ t' e, μR d =
        ∑ p ∈ s'.sigma t', μR p.1 * μR p.2 := by
    simp [s', t', sum_sigma, mul_sum]
  rw [hL, hR]
  refine sum_bij (fun p (_hp : p ∈ s.sigma t) => (⟨p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_sigma] at hp ⊢
    rcases hp with ⟨hp1, hp2⟩
    have hdmem : p.1 ∈ n.divisors := (mem_filter.mp hp1).1
    have hemem_le : p.2 ≤ u := (mem_filter.mp hp2).2
    have hdvd : p.1 ∣ n := dvd_of_mem_divisors hdmem
    have hevd : p.2 ∣ n / p.1 := dvd_of_mem_divisors (mem_filter.mp hp2).1
    have hde : p.1 * p.2 ∣ n := by
      rw [← Nat.mul_div_cancel' hdvd]
      exact mul_dvd_mul_left p.1 hevd
    have he_dvd_n : p.2 ∣ n := dvd_of_mul_left_dvd hde
    have hp2pos : 0 < p.2 := pos_of_dvd_of_pos he_dvd_n (pos_of_ne_zero hn)
    have hd_dvd_quot : p.1 ∣ n / p.2 := by
      rw [← Nat.mul_dvd_mul_iff_left hp2pos, Nat.mul_div_cancel' he_dvd_n, mul_comm]
      exact hde
    refine ⟨?_, ?_⟩
    · rw [mem_filter]
      exact ⟨mem_divisors.mpr ⟨he_dvd_n, hn⟩, hemem_le⟩
    · rw [mem_filter]
      exact ⟨mem_divisors.mpr ⟨hd_dvd_quot, div_ne_zero_of_dvd hn he_dvd_n⟩,
        (mem_filter.mp hp1).2⟩
  · intro p₁ _ p₂ _ h
    apply Sigma.ext
    · exact congrArg (fun r : Σ _ : ℕ, ℕ => r.2) h
    · exact heq_of_eq (congrArg (fun r : Σ _ : ℕ, ℕ => r.1) h)
  · intro p hp
    refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
    · rw [mem_sigma] at hp ⊢
      rcases hp with ⟨hp1, hp2⟩
      have hemem : p.1 ∈ n.divisors := (mem_filter.mp hp1).1
      have hdgt : u < p.2 := (mem_filter.mp hp2).2
      have he_le : p.1 ≤ u := (mem_filter.mp hp1).2
      have hevd : p.1 ∣ n := dvd_of_mem_divisors hemem
      have hdvd : p.2 ∣ n / p.1 := dvd_of_mem_divisors (mem_filter.mp hp2).1
      have hde : p.1 * p.2 ∣ n := by
        rw [← Nat.mul_div_cancel' hevd]
        exact mul_dvd_mul_left p.1 hdvd
      have hd_dvd_n : p.2 ∣ n := dvd_of_mul_left_dvd hde
      have hp2pos : 0 < p.2 := pos_of_dvd_of_pos hd_dvd_n (pos_of_ne_zero hn)
      have he_dvd_quot : p.1 ∣ n / p.2 := by
        rw [← Nat.mul_dvd_mul_iff_left hp2pos, Nat.mul_div_cancel' hd_dvd_n, mul_comm]
        exact hde
      refine ⟨?_, ?_⟩
      · exact mem_filter.mpr ⟨mem_divisors.mpr ⟨hd_dvd_n, hn⟩, hdgt⟩
      · exact mem_filter.mpr ⟨mem_divisors.mpr ⟨he_dvd_quot, div_ne_zero_of_dvd hn hd_dvd_n⟩, he_le⟩
    · rfl
  · intro p _
    ring

lemma pairSum_of_gt {n u : ℕ} (hn : n ≠ 0) (hnu : u < n) (hu : n < (u + 1) ^ 2) :
    pairSum n u = -μR n := by
  have hpair := pairSum_eq_divisors n u hn
  have hboth :
      ∑ d ∈ n.divisors.filter (u < ·),
        μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e = 0 := by
    refine sum_eq_zero fun d hd => ?_
    refine mul_eq_zero_of_right _ (sum_eq_zero fun e he => ?_)
    exfalso
    have hdgt : u < d := (mem_filter.mp hd).2
    have hegt : u < e := (mem_filter.mp he).2
    have hdvd := dvd_of_mem_divisors (mem_filter.mp hd).1
    have hevd := dvd_of_mem_divisors (mem_filter.mp he).1
    have hde : d * e ∣ n := by
      rw [← Nat.mul_div_cancel' hdvd]
      exact mul_dvd_mul_left d hevd
    have hge : (u + 1) ^ 2 ≤ d * e := by
      have hd1 : u + 1 ≤ d := succ_le_of_lt hdgt
      have he1 : u + 1 ≤ e := succ_le_of_lt hegt
      have : (u + 1) ^ 2 = (u + 1) * (u + 1) := by ring
      rw [this]
      exact Nat.mul_le_mul hd1 he1
    exact not_lt_of_ge (le_trans hge (le_of_dvd (pos_of_ne_zero hn) hde)) hu
  have hleft :
      ∑ d ∈ n.divisors.filter (· ≤ u),
        μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e = -pairSum n u := by
    rw [hpair]
    have hterm (d : ℕ) (hd : d ∈ n.divisors.filter (· ≤ u)) :
        μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e =
          -(μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e) := by
      have hdvd := dvd_of_mem_divisors (mem_filter.mp hd).1
      have hdlt : d < n := lt_of_le_of_lt (mem_filter.mp hd).2 hnu
      have hneq : n / d ≠ 1 := by
        intro h
        have := Nat.mul_div_cancel' hdvd
        rw [h, mul_one] at this
        exact absurd this (Nat.ne_of_lt hdlt)
      have hzero : ∑ e ∈ (n / d).divisors, μR e = 0 := by
        rw [sum_moebius_divisors, if_neg hneq]
      have hm : n / d ≠ 0 := div_ne_zero_of_dvd hn hdvd
      rw [divisors_sum_split (n / d) u hm] at hzero
      have hgt :
          ∑ e ∈ (n / d).divisors.filter (u < ·), μR e =
            -∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e := by
        have hle : ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e =
            -∑ e ∈ (n / d).divisors.filter (u < ·), μR e :=
          (add_eq_zero_iff_eq_neg).mp hzero
        exact ((neg_eq_iff_eq_neg).mpr hle).symm
      rw [hgt, mul_neg]
    exact (sum_congr rfl hterm).trans <| by rw [sum_neg_distrib]
  have hright :
      ∑ d ∈ n.divisors.filter (u < ·),
        μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e = -pairSum n u := by
    rw [mixed_swap n u hn]
    exact hleft
  have hfull := fullSum_eq n hn
  have hfour :
      ∑ d ∈ n.divisors, μR d * ∑ e ∈ (n / d).divisors, μR e =
        pairSum n u +
          ∑ d ∈ n.divisors.filter (· ≤ u),
            μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e +
          ∑ d ∈ n.divisors.filter (u < ·),
            μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e +
          ∑ d ∈ n.divisors.filter (u < ·),
            μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e := by
    have hdiv_ne (d : ℕ) (hd : d ∈ n.divisors) : n / d ≠ 0 :=
      div_ne_zero_of_dvd hn (dvd_of_mem_divisors hd)
    have hsplit_inner (d : ℕ) (hd : d ∈ n.divisors) :
        μR d * ∑ e ∈ (n / d).divisors, μR e =
          μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e +
            μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e := by
      rw [divisors_sum_split (n / d) u (hdiv_ne d hd), mul_add]
    rw [divisors_sum_split n u hn (fun d => μR d * ∑ e ∈ (n / d).divisors, μR e)]
    have hL :
        ∑ d ∈ n.divisors.filter (· ≤ u), μR d * ∑ e ∈ (n / d).divisors, μR e =
          ∑ d ∈ n.divisors.filter (· ≤ u),
            (μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e +
              μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e) :=
      sum_congr rfl fun d hd => hsplit_inner d (mem_filter.mp hd).1
    have hR :
        ∑ d ∈ n.divisors.filter (u < ·), μR d * ∑ e ∈ (n / d).divisors, μR e =
          ∑ d ∈ n.divisors.filter (u < ·),
            (μR d * ∑ e ∈ (n / d).divisors.filter (· ≤ u), μR e +
              μR d * ∑ e ∈ (n / d).divisors.filter (u < ·), μR e) :=
      sum_congr rfl fun d hd => hsplit_inner d (mem_filter.mp hd).1
    rw [hL, hR, sum_add_distrib, sum_add_distrib, hpair]
    ring
  rw [hfour, hleft, hright, hboth] at hfull
  linarith

lemma Icc_one_split (U N : ℕ) (hUN : U ≤ N) :
    Icc 1 U ∪ Icc (U + 1) N = Icc 1 N := by
  ext n
  constructor
  · intro hn
    rcases mem_union.mp hn with hn | hn
    · exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, le_trans (mem_Icc.mp hn).2 hUN⟩
    · exact mem_Icc.mpr ⟨le_trans (Nat.succ_le_succ (Nat.zero_le U)) (mem_Icc.mp hn).1,
        (mem_Icc.mp hn).2⟩
  · intro hn
    rcases mem_Icc.mp hn with ⟨h1, hN⟩
    by_cases hnU : n ≤ U
    · exact mem_union.mpr (Or.inl (mem_Icc.mpr ⟨h1, hnU⟩))
    · exact mem_union.mpr (Or.inr (mem_Icc.mpr ⟨Nat.succ_le_of_lt (lt_of_not_ge hnU), hN⟩))

lemma Icc_one_disjoint (U N : ℕ) : Disjoint (Icc 1 U) (Icc (U + 1) N) := by
  rw [disjoint_left]
  intro n hn hn'
  have hle : n ≤ U := (mem_Icc.mp hn).2
  have hge : U + 1 ≤ n := (mem_Icc.mp hn').1
  exact Nat.not_succ_le_self U (le_trans hge hle)

lemma sum_Icc_one_split (U N : ℕ) (hUN : U ≤ N) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, f n = ∑ n ∈ Icc 1 U, f n + ∑ n ∈ Icc (U + 1) N, f n := by
  rw [← Icc_one_split U N hUN, sum_union (Icc_one_disjoint U N)]

lemma range_eq_insert_Icc (m : ℕ) : range (m + 1) = insert 0 (Icc 1 m) := by
  ext k
  constructor
  · intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact mem_insert_self _ _
    · exact mem_insert.mpr (Or.inr (mem_Icc.mpr ⟨hk0, Nat.le_of_lt_succ (mem_range.mp hk)⟩))
  · intro hk
    rcases mem_insert.mp hk with rfl | hk
    · exact mem_range.mpr (Nat.succ_pos _)
    · exact mem_range.mpr (Nat.succ_le_succ (mem_Icc.mp hk).2)

lemma mertens_zero (a : ZMod q) : mertens a 0 = 0 := by
  simp [mertens, μR]

lemma mertens_eq_Icc (a : ZMod q) (m : ℕ) :
    mertens a m = ∑ k ∈ Icc 1 m, if ((k : ℕ) : ZMod q) = a then μR k else 0 := by
  rw [mertens, range_eq_insert_Icc, sum_insert (by simp)]
  simp [μR]

lemma pairSum_sqrt {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    pairSum n N.sqrt = if n ≤ N.sqrt then μR n else -μR n := by
  by_cases h : n ≤ N.sqrt
  · rw [if_pos h, pairSum_of_le (Nat.ne_of_gt hn) h]
  · rw [if_neg h, pairSum_of_gt (Nat.ne_of_gt hn) (lt_of_not_ge h)
      (lt_of_le_of_lt hnN (Nat.lt_succ_sqrt' N))]

lemma neg_indicator (n : ℕ) (a : ZMod q) :
    (if ((n : ℕ) : ZMod q) = a then -μR n else 0) =
      -(if ((n : ℕ) : ZMod q) = a then μR n else 0) := by
  by_cases h : ((n : ℕ) : ZMod q) = a <;> simp [h]

lemma pairSum_progression_sum (a : ZMod q) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if ((n : ℕ) : ZMod q) = a then pairSum n N.sqrt else 0) =
      2 * mertens a N.sqrt - mertens a N := by
  have hsqrt : N.sqrt ≤ N := Nat.sqrt_le_self _
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      (if ((n : ℕ) : ZMod q) = a then pairSum n N.sqrt else 0) =
        if ((n : ℕ) : ZMod q) = a then
          (if n ≤ N.sqrt then μR n else -μR n) else 0 := by
    rw [pairSum_sqrt (Nat.succ_le_iff.mp (mem_Icc.mp hn).1) (mem_Icc.mp hn).2]
  rw [sum_congr rfl hterm, sum_Icc_one_split N.sqrt N hsqrt]
  have hsmall (n : ℕ) (hn : n ∈ Icc 1 N.sqrt) :
      (if ((n : ℕ) : ZMod q) = a then (if n ≤ N.sqrt then μR n else -μR n) else 0) =
        if ((n : ℕ) : ZMod q) = a then μR n else 0 := by
    rw [if_pos (mem_Icc.mp hn).2]
  have hlarge (n : ℕ) (hn : n ∈ Icc (N.sqrt + 1) N) :
      (if ((n : ℕ) : ZMod q) = a then (if n ≤ N.sqrt then μR n else -μR n) else 0) =
        if ((n : ℕ) : ZMod q) = a then -μR n else 0 := by
    rw [if_neg (not_le_of_gt (Nat.lt_of_succ_le (mem_Icc.mp hn).1))]
  rw [sum_congr rfl hsmall, sum_congr rfl hlarge, sum_congr rfl (fun n _ => neg_indicator n a),
    sum_neg_distrib, ← mertens_eq_Icc]
  have hrest :
      ∑ n ∈ Icc (N.sqrt + 1) N, (if ((n : ℕ) : ZMod q) = a then μR n else 0) =
        mertens a N - mertens a N.sqrt := by
    rw [mertens_eq_Icc, mertens_eq_Icc, sum_Icc_one_split N.sqrt N hsqrt]
    ring
  rw [hrest]
  ring

lemma ite_pair_pull (c : Prop) [Decidable c] (u : ℕ) (n : ℕ) :
    (if c then pairSum n u else 0) =
      ∑ d ∈ Ioc 0 u, ∑ e ∈ Ioc 0 u,
        if d * e ∣ n ∧ c then μR d * μR e else 0 := by
  unfold pairSum
  by_cases hc : c
  · rw [if_pos hc]
    refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
    by_cases hde : d * e ∣ n
    · rw [if_pos hde, if_pos (And.intro hde hc)]
    · rw [if_neg hde, if_neg (fun h => hde h.1)]
  · rw [if_neg hc]
    symm
    refine sum_eq_zero fun d _ => ?_
    refine sum_eq_zero fun e _ => ?_
    exact if_neg (fun h => hc h.2)

lemma const_indicator_factor (s : Finset ℕ) (c : ℝ) (p : ℕ → Prop) [DecidablePred p] :
    ∑ n ∈ s, (if p n then c else 0) = c * ∑ n ∈ s, (if p n then (1 : ℝ) else 0) := by
  have hterm (n : ℕ) : (if p n then c else 0) = c * (if p n then (1 : ℝ) else 0) := by
    by_cases hn : p n <;> simp [hn]
  rw [sum_congr rfl fun n _ => hterm n, ← mul_sum]

lemma card_residue_mul (N d e : ℕ) (hde : 0 < d * e) (a : ZMod q) :
    ((Ioc 0 (N / (d * e))).filter fun r => ((d * e * r : ℕ) : ZMod q) = a).card =
      ((Icc 1 N).filter fun n => d * e ∣ n ∧ ((n : ℕ) : ZMod q) = a).card := by
  refine card_bij (fun r _ => d * e * r) ?_ ?_ ?_
  · intro r hr
    rcases mem_filter.mp hr with ⟨hrI, hres⟩
    rcases mem_Ioc.mp hrI with ⟨hr0, hrN⟩
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ⟨dvd_mul_right _ _, ?_⟩⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos hde hr0)
    · exact le_trans (Nat.mul_le_mul_left (d * e) hrN) (Nat.mul_div_le N (d * e))
    · exact hres
  · intro r₁ _ r₂ _ h
    exact Nat.eq_of_mul_eq_mul_left hde h
  · intro n hn
    rcases mem_filter.mp hn with ⟨hnI, hcond⟩
    rcases hcond with ⟨hdvd, hres⟩
    refine ⟨n / (d * e), mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, ?_⟩, Nat.mul_div_cancel' hdvd⟩
    · exact Nat.div_pos (Nat.le_of_dvd (Nat.succ_le_iff.mp (mem_Icc.mp hnI).1) hdvd) hde
    · exact Nat.div_le_div_right (mem_Icc.mp hnI).2
    · rw [Nat.mul_div_cancel' hdvd]
      exact hres

lemma indicator_sum_eq_count (N d e : ℕ) (hde : 0 < d * e) (a : ZMod q) :
    ∑ n ∈ Icc 1 N, (if d * e ∣ n ∧ ((n : ℕ) : ZMod q) = a then (1 : ℝ) else 0) =
      GRH.moebiusProgressionCount q a N d e := by
  have hcast (n : ℕ) :
      (if d * e ∣ n ∧ ((n : ℕ) : ZMod q) = a then (1 : ℝ) else 0) =
        (((if d * e ∣ n ∧ ((n : ℕ) : ZMod q) = a then 1 else 0 : ℕ) : ℝ)) := by
    by_cases h : d * e ∣ n ∧ ((n : ℕ) : ZMod q) = a <;> simp [h]
  rw [sum_congr rfl fun n _ => hcast n, ← Nat.cast_sum, ← card_filter,
    (card_residue_mul N d e hde a).symm]
  rfl

lemma progression_of_pairSum (a : ZMod q) (N U : ℕ) :
    ∑ n ∈ Icc 1 N, (if ((n : ℕ) : ZMod q) = a then pairSum n U else 0) =
      ∑ d ∈ Ioc 0 U, ∑ e ∈ Ioc 0 U,
        μR d * μR e * GRH.moebiusProgressionCount q a N d e := by
  have hterm (n : ℕ) :
      (if ((n : ℕ) : ZMod q) = a then pairSum n U else 0) =
        ∑ d ∈ Ioc 0 U, ∑ e ∈ Ioc 0 U,
          if d * e ∣ n ∧ ((n : ℕ) : ZMod q) = a then μR d * μR e else 0 :=
    ite_pair_pull _ U n
  rw [sum_congr rfl fun n _ => hterm n, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_comm]
  refine sum_congr rfl fun e he => ?_
  have hde : 0 < d * e :=
    Nat.mul_pos (Nat.succ_le_iff.mp (mem_Ioc.mp hd).1) (Nat.succ_le_iff.mp (mem_Ioc.mp he).1)
  rw [const_indicator_factor, indicator_sum_eq_count N d e hde]

def mainTerm (modulus : ℕ) [NeZero modulus] (N d e : ℕ) : ℝ :=
  if IsUnit ((d : ℕ) : ZMod modulus) ∧ IsUnit ((e : ℕ) : ZMod modulus) then
    (1 / (modulus : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0

lemma unit_main_factor (N d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    μR d * (μR e * mainTerm q N d e) =
      ((N : ℝ) / q) * (if IsUnit ((d : ℕ) : ZMod q) then μR d / (d : ℝ) else 0) *
        (if IsUnit ((e : ℕ) : ZMod q) then μR e / (e : ℝ) else 0) := by
  by_cases hdU : IsUnit ((d : ℕ) : ZMod q) <;> by_cases heU : IsUnit ((e : ℕ) : ZMod q)
  · rw [mainTerm, if_pos (And.intro hdU heU), if_pos hdU, if_pos heU]
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
    have he0 : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt he)
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp [hd0, he0, hq0]
  · simp [mainTerm, hdU, heU]
  · simp [mainTerm, hdU, heU]
  · simp [mainTerm, hdU, heU]

lemma main_sum_eq_square (N U : ℕ) :
    ∑ d ∈ Ioc 0 U, μR d * ∑ e ∈ Ioc 0 U, μR e * mainTerm q N d e =
      ((N : ℝ) / q) * (GRH.reducedMoebiusHarmonic q U) ^ 2 := by
  have hterm (d e : ℕ) (hd : d ∈ Ioc 0 U) (he : e ∈ Ioc 0 U) :
      μR d * (μR e * mainTerm q N d e) =
        ((N : ℝ) / q) * (if IsUnit ((d : ℕ) : ZMod q) then μR d / (d : ℝ) else 0) *
          (if IsUnit ((e : ℕ) : ZMod q) then μR e / (e : ℝ) else 0) :=
    unit_main_factor N d e (Nat.succ_le_iff.mp (mem_Ioc.mp hd).1)
      (Nat.succ_le_iff.mp (mem_Ioc.mp he).1)
  have hsum :
      ∑ d ∈ Ioc 0 U, ∑ e ∈ Ioc 0 U, μR d * (μR e * mainTerm q N d e) =
        ((N : ℝ) / q) *
          (∑ d ∈ Ioc 0 U, if IsUnit ((d : ℕ) : ZMod q) then μR d / (d : ℝ) else 0) *
            (∑ e ∈ Ioc 0 U, if IsUnit ((e : ℕ) : ZMod q) then μR e / (e : ℝ) else 0) := by
    rw [sum_congr rfl fun d hd =>
      (sum_congr rfl fun e he => hterm d e hd he).trans (by rw [← mul_sum]),
      ← sum_mul, ← mul_sum]
  have hmul :
      ∑ d ∈ Ioc 0 U, μR d * ∑ e ∈ Ioc 0 U, μR e * mainTerm q N d e =
        ∑ d ∈ Ioc 0 U, ∑ e ∈ Ioc 0 U, μR d * (μR e * mainTerm q N d e) := by
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
  have hH :
      GRH.reducedMoebiusHarmonic q U =
        ∑ d ∈ Ioc 0 U, if IsUnit ((d : ℕ) : ZMod q) then μR d / (d : ℝ) else 0 := by
    unfold GRH.reducedMoebiusHarmonic
    refine sum_congr rfl fun d _ => ?_
    by_cases h : IsUnit ((d : ℕ) : ZMod q)
    · simp [h, μR]
    · simp [h]
  rw [hmul, hsum, ← hH]
  ring

lemma count_sum_eq (a : ZMod q) (N : ℕ) :
    ∑ d ∈ Ioc 0 N.sqrt, μR d *
        ∑ e ∈ Ioc 0 N.sqrt, μR e * GRH.moebiusProgressionCount q a N d e =
      ∑ n ∈ Icc 1 N, (if ((n : ℕ) : ZMod q) = a then pairSum n N.sqrt else 0) := by
  refine Eq.trans ?_ (progression_of_pairSum a N N.sqrt).symm
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  ring

lemma centered_split (a : ZMod q) (N : ℕ) :
    GRH.centeredMoebiusBilinear q a N =
      (∑ d ∈ Ioc 0 N.sqrt, μR d *
          ∑ e ∈ Ioc 0 N.sqrt, μR e * GRH.moebiusProgressionCount q a N d e) -
        (∑ d ∈ Ioc 0 N.sqrt, μR d * ∑ e ∈ Ioc 0 N.sqrt, μR e * mainTerm q N d e) := by
  unfold GRH.centeredMoebiusBilinear mainTerm
  have hinner (d : ℕ) :
      ∑ e ∈ Ioc 0 N.sqrt, μR e *
          (GRH.moebiusProgressionCount q a N d e -
            if IsUnit ((d : ℕ) : ZMod q) ∧ IsUnit ((e : ℕ) : ZMod q) then
              (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
        ∑ e ∈ Ioc 0 N.sqrt, μR e * GRH.moebiusProgressionCount q a N d e -
          ∑ e ∈ Ioc 0 N.sqrt, μR e *
            (if IsUnit ((d : ℕ) : ZMod q) ∧ IsUnit ((e : ℕ) : ZMod q) then
              (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) := by
    have hterm (e : ℕ) :
        μR e * (GRH.moebiusProgressionCount q a N d e -
            if IsUnit ((d : ℕ) : ZMod q) ∧ IsUnit ((e : ℕ) : ZMod q) then
              (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
          μR e * GRH.moebiusProgressionCount q a N d e -
            μR e * (if IsUnit ((d : ℕ) : ZMod q) ∧ IsUnit ((e : ℕ) : ZMod q) then
              (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) :=
      mul_sub _ _ _
    rw [sum_congr rfl fun e _ => hterm e, sum_sub_distrib]
  let countSum : ℕ → ℝ := fun d =>
    μR d * ∑ e ∈ Ioc 0 N.sqrt, μR e * GRH.moebiusProgressionCount q a N d e
  let mainSum : ℕ → ℝ := fun d =>
    μR d * ∑ e ∈ Ioc 0 N.sqrt, μR e *
      (if IsUnit ((d : ℕ) : ZMod q) ∧ IsUnit ((e : ℕ) : ZMod q) then
        (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)
  have hdiff : ∑ d ∈ Ioc 0 N.sqrt, (countSum d - mainSum d) =
      ∑ d ∈ Ioc 0 N.sqrt, countSum d - ∑ d ∈ Ioc 0 N.sqrt, mainSum d :=
    sum_sub_distrib (f := countSum) (g := mainSum)
  have hrewrite :
      ∑ d ∈ Ioc 0 N.sqrt, μR d * ∑ e ∈ Ioc 0 N.sqrt, μR e *
          (GRH.moebiusProgressionCount q a N d e -
            if IsUnit ((d : ℕ) : ZMod q) ∧ IsUnit ((e : ℕ) : ZMod q) then
              (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
        ∑ d ∈ Ioc 0 N.sqrt, (countSum d - mainSum d) := by
    refine sum_congr rfl fun d _ => ?_
    rw [hinner d, mul_sub]
  have hcast (n : ℕ) : (moebius n : ℝ) = μR n := rfl
  simp_rw [hcast]
  rw [hrewrite, hdiff]

lemma centered_identity (a : ZMod q) (N : ℕ) :
    GRH.centeredMoebiusBilinear q a N =
      2 * mertens a N.sqrt - mertens a N -
        ((N : ℝ) / q) * (GRH.reducedMoebiusHarmonic q N.sqrt) ^ 2 := by
  rw [centered_split, count_sum_eq, pairSum_progression_sum, main_sum_eq_square]

lemma sqrt_on_block (u j : ℕ) (hj : j < 2 * u + 1) : (u ^ 2 + j).sqrt = u := by
  have hj' : j ≤ u + u := by omega
  exact Nat.sqrt_add_eq' u hj'

lemma block_length_ne_zero (u : ℕ) : ((2 * u + 1 : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.succ_ne_zero (2 * u))

lemma sum_block_base (u : ℕ) :
    ∑ j ∈ range (2 * u + 1), ((u ^ 2 + j : ℕ) : ℝ) =
      ((2 * u + 1 : ℕ) : ℝ) * ((u : ℝ) ^ 2 + (u : ℝ)) := by
  have hsplit : ∀ j : ℕ, ((u ^ 2 + j : ℕ) : ℝ) = (u : ℝ) ^ 2 + (j : ℝ) := by
    intro j
    push_cast
    ring
  simp_rw [hsplit, sum_add_distrib, sum_const, card_range]
  have hnat : ∑ j ∈ range (2 * u + 1), j = (2 * u + 1) * u := by
    rw [Finset.sum_range_id]
    have hsub : (2 * u + 1) - 1 = 2 * u := by omega
    rw [hsub, Nat.mul_div_assoc (2 * u + 1) ⟨u, rfl⟩]
    have hdiv : 2 * u / 2 = u :=
      Nat.div_eq_of_eq_mul_right (by decide : 0 < 2) (by ring)
    rw [hdiv]
  have hcast : ∑ j ∈ range (2 * u + 1), (j : ℝ) =
      ((2 * u + 1 : ℕ) : ℝ) * (u : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hnat
    simpa [Nat.cast_sum, Nat.cast_mul] using h
  rw [hcast]
  push_cast
  ring_nf

lemma mean_identity (a : ZMod q) (u : ℕ) :
    (∑ j ∈ range (2 * u + 1), GRH.centeredMoebiusBilinear q a (u ^ 2 + j)) /
        ((2 * u + 1 : ℕ) : ℝ) =
      2 * mertens a u -
        (∑ j ∈ range (2 * u + 1), mertens a (u ^ 2 + j)) / ((2 * u + 1 : ℕ) : ℝ) -
        (((u : ℝ) ^ 2 + (u : ℝ)) / q) * (GRH.reducedMoebiusHarmonic q u) ^ 2 := by
  set L : ℝ := ((2 * u + 1 : ℕ) : ℝ)
  have hL : L ≠ 0 := block_length_ne_zero u
  have hpoint : ∀ j ∈ range (2 * u + 1),
      GRH.centeredMoebiusBilinear q a (u ^ 2 + j) =
        2 * mertens a u - mertens a (u ^ 2 + j) -
          (((u ^ 2 + j : ℕ) : ℝ) / q) * (GRH.reducedMoebiusHarmonic q u) ^ 2 := by
    intro j hj
    have hs := sqrt_on_block u j (mem_range.mp hj)
    have hid := centered_identity a (u ^ 2 + j)
    rw [hs] at hid
    exact hid
  rw [sum_congr rfl hpoint, sum_sub_distrib]
  have hconst : ∑ j ∈ range (2 * u + 1), (2 * mertens a u - mertens a (u ^ 2 + j)) =
      ((2 * u + 1 : ℕ) : ℝ) * (2 * mertens a u) -
        ∑ j ∈ range (2 * u + 1), mertens a (u ^ 2 + j) := by
    have hsub' (j : ℕ) : 2 * mertens a u - mertens a (u ^ 2 + j) =
        2 * mertens a u + -mertens a (u ^ 2 + j) := by
      ring
    rw [sum_congr rfl fun j _ => hsub' j, sum_add_distrib, sum_neg_distrib, sum_const, card_range]
    push_cast
    ring_nf
  rw [hconst]
  set H := GRH.reducedMoebiusHarmonic q u
  have hmain : ∑ j ∈ range (2 * u + 1),
      (((u ^ 2 + j : ℕ) : ℝ) / q) * H ^ 2 =
      (∑ j ∈ range (2 * u + 1), ((u ^ 2 + j : ℕ) : ℝ)) * (H ^ 2 / q) := by
    have hterm (j : ℕ) : (((u ^ 2 + j : ℕ) : ℝ) / q) * H ^ 2 =
        ((u ^ 2 + j : ℕ) : ℝ) * (H ^ 2 / q) := by
      ring
    rw [sum_congr rfl fun j _ => hterm j, ← sum_mul]
  rw [hmain, sum_block_base]
  field_simp [hL]
  ring

lemma block_power (u : ℕ) (σ : ℝ) (hhalf : 1 / 2 < σ) (hσ : σ < 1) :
    ((u : ℝ) + 1) ^ (2 * σ - 2) * ((u : ℝ) ^ 2 + (u : ℝ)) ≤
      2 * ((u : ℝ) ^ 2 + 1) ^ σ := by
  have hneg : 2 * σ - 2 ≤ 0 := by linarith
  have hσ0 : 0 ≤ σ := by linarith
  by_cases hu : u = 0
  · simp [hu, Real.one_rpow, mul_zero, two_mul]
  · have hu0 : (0 : ℝ) < u := by exact_mod_cast Nat.pos_of_ne_zero hu
    have hbase : (u : ℝ) ≤ (u : ℝ) + 1 := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hu0 hbase hneg
    have hlin : (u : ℝ) ^ 2 + (u : ℝ) ≤ 2 * (u : ℝ) ^ 2 := by
      have h2 : (u : ℝ) + 1 ≤ 2 * (u : ℝ) := by
        have : (1 : ℝ) ≤ u := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hu
        linarith
      nlinarith
    have hnatPow : (u : ℝ) ^ 2 = (u : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast (u : ℝ) 2).symm
    have hmul1 := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (u : ℝ) ^ 2 + (u : ℝ))
    have hmul2 := mul_le_mul_of_nonneg_left hlin
      (Real.rpow_nonneg (Nat.cast_nonneg u) (2 * σ - 2))
    have hprod : (u : ℝ) ^ (2 * σ - 2) * (2 * (u : ℝ) ^ 2) = 2 * (u : ℝ) ^ (2 * σ) := by
      rw [hnatPow, mul_left_comm, ← Real.rpow_add hu0]
      ring_nf
    have hsq : (u : ℝ) ^ (2 * σ) = ((u : ℝ) ^ 2) ^ σ := by
      rw [hnatPow, ← Real.rpow_mul (Nat.cast_nonneg u)]
    have hmono : ((u : ℝ) ^ 2) ^ σ ≤ ((u : ℝ) ^ 2 + 1) ^ σ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hσ0
    have hlast : 2 * (u : ℝ) ^ (2 * σ) ≤ 2 * ((u : ℝ) ^ 2 + 1) ^ σ := by
      rw [hsq]
      exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    linarith [hmul1, hmul2, hprod, hlast]

end MoebiusCentered

end

noncomputable section

open Finset MoebiusCentered

theorem solution (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (σ : ℝ) (hhalf : 1 / 2 < σ) (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
      |(∑ j ∈ range (2 * u + 1), GRH.centeredMoebiusBilinear q a (u ^ 2 + j)) /
          ((2 * u + 1 : ℕ) : ℝ)| ≤
        C * ((u : ℝ) ^ 2 + 1) ^ σ := by
  have hlt1 : σ < 1 := by
    have hbound : (0.8749570698 : ℝ) < 1 := by norm_num
    exact lt_of_le_of_lt hcap hbound
  have hle1 : σ ≤ 1 := le_of_lt hlt1
  obtain ⟨K, hK, hLiouville⟩ :=
    GRH.reduced_liouville_harmonic_power_decay q σ hhalf hlt1
  let Z : ℝ := ∑' d : ℕ, ((d : ℝ) ^ (2 * σ))⁻¹
  have hZ : 0 ≤ Z :=
    tsum_nonneg fun d => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  let Cμ : ℝ := K * Z
  have hCμ : 0 ≤ Cμ := mul_nonneg hK hZ
  obtain ⟨Cm, hCm, hPartial⟩ :=
    GRH.moebius_square_block_partial_sum_mean q a ha σ hhalf hcap
  refine ⟨Cm + 2 * Cμ ^ 2, ?_, ?_⟩
  · nlinarith [sq_nonneg Cμ]
  · intro u
    have hmean := mean_identity (q := q) a u
    have hH := GRH.reduced_moebius_harmonic_le_of_liouville_harmonic_le q σ K hhalf hle1 hK
      hLiouville u
    rw [hmean]
    have hD : |2 * mertens a u -
          (∑ j ∈ range (2 * u + 1), mertens a (u ^ 2 + j)) / ((2 * u + 1 : ℕ) : ℝ)| ≤
        Cm * ((u : ℝ) ^ 2 + 1) ^ σ := by
      simpa [mertens, μR] using hPartial u
    have hsub : |2 * mertens a u -
          (∑ j ∈ range (2 * u + 1), mertens a (u ^ 2 + j)) / ((2 * u + 1 : ℕ) : ℝ) -
          (((u : ℝ) ^ 2 + (u : ℝ)) / q) * (GRH.reducedMoebiusHarmonic q u) ^ 2| ≤
        |2 * mertens a u -
          (∑ j ∈ range (2 * u + 1), mertens a (u ^ 2 + j)) / ((2 * u + 1 : ℕ) : ℝ)| +
          |(((u : ℝ) ^ 2 + (u : ℝ)) / q) * (GRH.reducedMoebiusHarmonic q u) ^ 2| := by
      have h := norm_sub_le
        (2 * mertens a u -
          (∑ j ∈ range (2 * u + 1), mertens a (u ^ 2 + j)) / ((2 * u + 1 : ℕ) : ℝ))
        ((((u : ℝ) ^ 2 + (u : ℝ)) / q) * (GRH.reducedMoebiusHarmonic q u) ^ 2)
      simp only [Real.norm_eq_abs] at h
      exact h
    refine hsub.trans ?_
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hden : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hHarm : |(((u : ℝ) ^ 2 + (u : ℝ)) / q) * (GRH.reducedMoebiusHarmonic q u) ^ 2| ≤
        2 * Cμ ^ 2 * ((u : ℝ) ^ 2 + 1) ^ σ := by
      have hnn : 0 ≤ ((u : ℝ) ^ 2 + (u : ℝ)) / q :=
        div_nonneg (by positivity) (le_of_lt hden)
      rw [abs_mul, abs_of_nonneg hnn, abs_of_nonneg (sq_nonneg _)]
      have hsq : (GRH.reducedMoebiusHarmonic q u) ^ 2 ≤
          (Cμ * ((u : ℝ) + 1) ^ (σ - 1)) ^ 2 := by
        rw [← sq_abs]
        have habs : |GRH.reducedMoebiusHarmonic q u| ≤ Cμ * ((u : ℝ) + 1) ^ (σ - 1) := by
          simpa [Cμ, Z] using hH
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      have hcoeff : ((u : ℝ) ^ 2 + (u : ℝ)) / q ≤ (u : ℝ) ^ 2 + (u : ℝ) := by
        rw [div_le_iff₀ hden]
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsq hnn
      have hdrop := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (GRH.reducedMoebiusHarmonic q u))
      have hpow := block_power u σ hhalf hlt1
      have hfinal : (Cμ * ((u : ℝ) + 1) ^ (σ - 1)) ^ 2 * ((u : ℝ) ^ 2 + (u : ℝ)) ≤
          2 * Cμ ^ 2 * ((u : ℝ) ^ 2 + 1) ^ σ := by
        have hC : 0 ≤ Cμ ^ 2 := sq_nonneg Cμ
        have hrewrite : (Cμ * ((u : ℝ) + 1) ^ (σ - 1)) ^ 2 =
            Cμ ^ 2 * ((u : ℝ) + 1) ^ (2 * σ - 2) := by
          rw [mul_pow]
          have hpos : (0 : ℝ) ≤ (u : ℝ) + 1 := by positivity
          have hexp : (((u : ℝ) + 1) ^ (σ - 1)) ^ 2 =
              ((u : ℝ) + 1) ^ (2 * (σ - 1)) := by
            rw [← Real.rpow_natCast (((u : ℝ) + 1) ^ (σ - 1)) 2,
              ← Real.rpow_mul hpos]
            congr 1
            ring
          rw [hexp]
          ring_nf
        have hscale := mul_le_mul_of_nonneg_left hpow hC
        rw [hrewrite]
        linarith
      calc
        ((u : ℝ) ^ 2 + (u : ℝ)) / q * (GRH.reducedMoebiusHarmonic q u) ^ 2
            ≤ ((u : ℝ) ^ 2 + (u : ℝ)) * (GRH.reducedMoebiusHarmonic q u) ^ 2 := hdrop
        _ ≤ ((u : ℝ) ^ 2 + (u : ℝ)) * (Cμ * ((u : ℝ) + 1) ^ (σ - 1)) ^ 2 := by
              have hsq' := mul_le_mul_of_nonneg_left hsq
                (by positivity : 0 ≤ (u : ℝ) ^ 2 + (u : ℝ))
              simpa [mul_comm, mul_left_comm, mul_assoc] using hsq'
        _ ≤ 2 * Cμ ^ 2 * ((u : ℝ) ^ 2 + 1) ^ σ := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hfinal
    linarith
