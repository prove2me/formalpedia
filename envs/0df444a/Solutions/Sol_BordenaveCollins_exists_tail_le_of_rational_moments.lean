-- Prove2me | solution 1 for BordenaveCollins.exists_tail_le_of_rational_moments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:20:43.334556+00:00
-- url     : https://prove2.me/submissions/71c4ff19-db40-457c-b4cb-7feae8a8d6db

import Mathlib
import Theorems.Thm_StrongConv_cNorm_iteratedDeriv_div_le
import Theorems.Thm_StrongConv_cNorm_le_two_mul_sSup_of_subset_add
import Theorems.Thm_StrongConv_abs_coeff_zero_le_and_sum_le_lpNormCircle
import Theorems.Thm_StrongConv_tfae_extends_csDistribution
import Theorems.Thm_StrongConv_supp_subset_Icc_limsup
import Theorems.Thm_StrongConv_vanishesNear_supp

section
/-!
# Part A, module 1: the analytic core of the polynomial method

A sequence `F n = f(1/n)/g(1/n)` given by a rational function of bounded degree, bounded by `s`,
has a first-order expansion in `1/n` with explicit constants (CGTvH Lemmas 4.2, 4.3 and Taylor).
-/

open Polynomial Filter Topology StrongConv
open scoped Pointwise

namespace BordenaveCollins.PartA

lemma density_lemma (M : ℕ) (hM : 0 < M) (q : ℝ) (hq0 : 0 < q) (hq : 4 * q ^ 2 ≤ 2 * M) :
    Set.Icc (0 : ℝ) (1 / M) ⊆ {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)} +
      Set.Icc (-((1 / (M : ℝ)) / (4 * q ^ 2))) ((1 / (M : ℝ)) / (4 * q ^ 2)) := by
  intro y hy
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := (1 / (M : ℝ)) / (4 * q ^ 2) with hδ
  have hq2 : 0 < 4 * q ^ 2 := by positivity
  have hδD : 1 / (2 * (M : ℝ) ^ 2) ≤ δ := by
    rw [hδ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have key : ∃ x ∈ {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)}, |y - x| ≤ δ := by
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      obtain ⟨n, hn⟩ := exists_nat_ge (1 / δ)
      refine ⟨1 / ((max n M + 1 : ℕ) : ℝ), ⟨_, by omega, rfl⟩, ?_⟩
      have hn' : (1 / δ) ≤ ((max n M + 1 : ℕ) : ℝ) := by
        refine hn.trans ?_
        have : n ≤ max n M + 1 := by omega
        exact_mod_cast this
      have hpos : (0 : ℝ) < ((max n M + 1 : ℕ) : ℝ) := by positivity
      rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hδpos] at hn'
      linarith
    · have hyM : (M : ℝ) ≤ 1 / y := by
        rw [le_div_iff₀ hpos]
        have := hy.2
        rw [le_div_iff₀ hMp] at this
        linarith
      set n := ⌊1 / y⌋₊ with hn
      have hnM : M ≤ n := Nat.le_floor hyM
      have hn1 : (n : ℝ) ≤ 1 / y := Nat.floor_le (by positivity)
      have hn2 : 1 / y < n + 1 := Nat.lt_floor_add_one _
      have hnp : (0 : ℝ) < n := by
        have : (M : ℝ) ≤ n := by exact_mod_cast hnM
        linarith
      have hy1 : y ≤ 1 / (n : ℝ) := by
        rw [le_div_iff₀ hnp]; rw [le_div_iff₀ hpos] at hn1; linarith
      have hy2 : 1 / ((n : ℝ) + 1) < y := by
        rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hpos] at hn2; linarith
      have hgap : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) ≤ 1 / (M : ℝ) ^ 2 := by
        have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * (n + 1)) := by
          field_simp; ring
        rw [this]
        have hnM' : (M : ℝ) ≤ n := by exact_mod_cast hnM
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have hD : 1 / (M : ℝ) ^ 2 = 2 * (1 / (2 * (M : ℝ) ^ 2)) := by field_simp
      by_cases hc : 1 / (n : ℝ) - y ≤ 1 / (2 * (M : ℝ) ^ 2)
      · refine ⟨1 / (n : ℝ), ⟨n, hnM, rfl⟩, ?_⟩
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · push Not at hc
        refine ⟨1 / ((n + 1 : ℕ) : ℝ), ⟨n + 1, by omega, rfl⟩, ?_⟩
        push_cast
        rw [abs_of_nonneg (by linarith)]
        linarith
  obtain ⟨x, hx, hxy⟩ := key
  refine Set.mem_add.2 ⟨x, hx, y - x, ?_, by ring⟩
  rw [Set.mem_Icc]
  exact abs_le.1 hxy

lemma cNorm_zero_eq (h : ℝ → ℝ) (a b : ℝ) :
    cNorm 0 h a b = sSup ((fun x => |iteratedDeriv 0 h x|) '' Set.Icc a b) := by
  simp [cNorm, supOn]

lemma abs_le_cNorm_zero (h : ℝ → ℝ) (a b : ℝ) (hc : ContinuousOn (iteratedDeriv 0 h) (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) : |iteratedDeriv 0 h x| ≤ cNorm 0 h a b := by
  rw [cNorm_zero_eq]
  exact le_csSup (isCompact_Icc.bddAbove_image hc.abs) ⟨x, hx, rfl⟩

lemma polyc {n : ℕ} (p : ℝ[X]) : ContDiff ℝ n (fun x => p.eval x) := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) p (n : WithTop ℕ∞)
  simpa only [Polynomial.coe_aeval_eq_eval] using this

lemma poly_div_contDiffAt (f g : ℝ[X]) (n : ℕ) (y : ℝ) (hy : g.eval y ≠ 0) :
    ContDiffAt ℝ n (fun x => f.eval x / g.eval x) y :=
  (polyc f).contDiffAt.div (polyc g).contDiffAt hy

lemma poly_div_continuousOn_iteratedDeriv (f g : ℝ[X]) (b : ℝ) (hb : 0 < b)
    (hg0 : ∀ x ∈ Set.Icc 0 b, g.eval x ≠ 0) (m : ℕ) :
    ContinuousOn (iteratedDeriv m (fun x => f.eval x / g.eval x)) (Set.Icc 0 b) := by
  have hcd : ContDiffOn ℝ m (fun x => f.eval x / g.eval x) (Set.Icc 0 b) :=
    fun y hy => (poly_div_contDiffAt f g m y (hg0 y hy)).contDiffWithinAt
  have := hcd.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hb)
  refine this.congr fun y hy => ?_
  exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
    (poly_div_contDiffAt f g m y (hg0 y hy)) hy).symm

lemma taylor_step (Ψ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (n : ℕ)
    (hcd : ∀ y ∈ Set.Icc 0 x, ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ y) (C : ℝ)
    (hC : ∀ y ∈ Set.Icc 0 x, |iteratedDeriv (n + 1) Ψ y| ≤ C) :
    |Ψ x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k| ≤
      C * x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hu : Set.uIcc (0 : ℝ) x = Set.Icc 0 x := Set.uIcc_of_le hx.le
  have hcdOn : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ (Set.uIcc 0 x) := by
    rw [hu]; exact fun y hy => (hcd y hy).contDiffWithinAt
  obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx.ne hcdOn
  have hx'I : x' ∈ Set.Icc 0 x := by
    rw [Set.uIoo_of_le hx.le] at hx'
    exact ⟨hx'.1.le, hx'.2.le⟩
  have htay : taylorWithinEval Ψ n (Set.uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
    rw [hu, smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      ((hcd 0 ⟨le_rfl, hx.le⟩).of_le (by exact_mod_cast (by omega : k ≤ n + 1))) ⟨le_rfl, hx.le⟩]
    rw [sub_zero]; field_simp
  rw [htay] at hrem
  rw [hrem, sub_zero, abs_div, abs_mul, abs_pow, abs_of_pos hx,
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (hC x' hx'I) (by positivity)

/-- The analytic core: a first-order expansion of `F n = f(1/n)/g(1/n)`. -/
lemma core_est (Q : ℕ) (hQ : 1 ≤ Q) (f g : ℝ[X]) (hfq : f.natDegree ≤ Q) (hgq : g.natDegree ≤ Q)
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) (1 / (2 * (Q : ℝ) ^ 2)), 1 / 2 ≤ g.eval x ∧ g.eval x ≤ 1)
    (F : ℕ → ℝ) (s : ℝ)
    (hF : ∀ n : ℕ, 2 * Q ^ 2 ≤ n → F n = f.eval (1 / (n : ℝ)) / g.eval (1 / (n : ℝ)))
    (hs : ∀ n : ℕ, |F n| ≤ s) :
    ∃ l0 l1 : ℝ, |l0| ≤ 4 * s ∧ |l1| ≤ 80 * (Q : ℝ) ^ 4 * s ∧
      ∀ n : ℕ, 2 * Q ^ 2 ≤ n → |F n - l0 - l1 / n| ≤ 1600 * (Q : ℝ) ^ 8 * s / (n : ℝ) ^ 2 := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set M : ℕ := 2 * Q ^ 2 with hMdef
  have hMc : (M : ℝ) = 2 * (Q : ℝ) ^ 2 := by rw [hMdef]; push_cast; ring
  have hQ2 : 1 ≤ (Q : ℝ) ^ 2 := one_le_pow₀ hQ1
  have hMp : (0 : ℝ) < M := by rw [hMc]; positivity
  have hMpos : 0 < M := by exact_mod_cast hMp
  rw [← hMc] at hg
  set Ψ : ℝ → ℝ := fun x => f.eval x / g.eval x with hΨ
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0)
  have hb : (0 : ℝ) < 1 / M := by positivity
  have hg0 : ∀ x ∈ Set.Icc (0 : ℝ) (1 / M), g.eval x ≠ 0 := fun x hx => by
    have := (hg x hx).1; intro h; rw [h] at this; norm_num at this
  have hfI : ∀ n : ℕ, M ≤ n → |f.eval (1 / (n : ℝ))| ≤ s := by
    intro n hn
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    have hx1 : 1 / (n : ℝ) ≤ 1 / (M : ℝ) :=
      one_div_le_one_div_of_le hMp (by exact_mod_cast hn)
    obtain ⟨hg1, hg2⟩ := hg _ ⟨by positivity, hx1⟩
    have hFn := hF n hn
    have : f.eval (1 / (n : ℝ)) = F n * g.eval (1 / (n : ℝ)) := by
      rw [hFn]; field_simp
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < g.eval (1 / (n : ℝ)))]
    calc |F n| * g.eval (1 / (n : ℝ)) ≤ s * 1 :=
          mul_le_mul (hs n) hg2 (by linarith) hs0
      _ = s := mul_one s
  set I : Set ℝ := {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)} with hI
  have hIsub : I ⊆ Set.Icc 0 (1 / (M : ℝ)) := by
    rintro x ⟨n, hn, rfl⟩
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    exact ⟨by positivity, one_div_le_one_div_of_le hMp (by exact_mod_cast hn)⟩
  have hdens := density_lemma M hMpos (Q : ℝ) (by linarith) (by rw [hMc]; linarith)
  have h42 := cNorm_le_two_mul_sSup_of_subset_add Q f hfq (1 / (M : ℝ)) hb I hIsub hdens
  have hsup : sSup ((fun x => |f.eval x|) '' I) ≤ s := by
    refine csSup_le ⟨_, 1 / (M : ℝ), ⟨M, le_rfl, rfl⟩, rfl⟩ ?_
    rintro _ ⟨x, ⟨n, hn, rfl⟩, rfl⟩
    exact hfI n hn
  have hcf : cNorm 0 (fun x => f.eval x) 0 (1 / (M : ℝ)) ≤ 2 * s := by linarith
  have hfcont : ContinuousOn (iteratedDeriv 0 (fun x => f.eval x)) (Set.Icc 0 (1 / (M : ℝ))) := by
    rw [iteratedDeriv_zero]; exact (polyc (n := 0) f).continuous.continuousOn
  have hΨ4 : cNorm 0 Ψ 0 (1 / (M : ℝ)) ≤ 4 * s := by
    rw [cNorm_zero_eq]
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hg1, hg2⟩ := hg x hx
    have h1 := abs_le_cNorm_zero (fun x => f.eval x) 0 (1 / (M : ℝ)) hfcont x hx
    rw [iteratedDeriv_zero] at h1 ⊢
    simp only [hΨ]
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (f.eval x)]
  set S := sSup {t | ∃ x ∈ Set.Icc (0 : ℝ) (1 / M), ∃ y ∈ Set.Icc (0 : ℝ) (1 / M),
    t = |g.eval x / g.eval y|} with hS
  have hS0 : 0 ≤ S := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩; exact abs_nonneg _
  have hS2 : S ≤ 2 := by
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨hx1, hx2⟩ := hg x hx
    obtain ⟨hy1, hy2⟩ := hg y hy
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), abs_of_pos (by linarith : 0 < g.eval y),
      div_le_iff₀ (by linarith)]
    linarith
  have hbase : 5 * S * (Q : ℝ) ^ 2 / (1 / (M : ℝ)) ≤ 20 * (Q : ℝ) ^ 4 := by
    have e : 5 * S * (Q : ℝ) ^ 2 / (1 / (M : ℝ)) = 5 * S * (Q : ℝ) ^ 2 * M := by
      field_simp
    rw [e, hMc]
    nlinarith [mul_le_mul_of_nonneg_right hS2 (by positivity : (0 : ℝ) ≤ (Q : ℝ) ^ 2 * (Q : ℝ) ^ 2)]
  have hbase0 : 0 ≤ 5 * S * (Q : ℝ) ^ 2 / (1 / (M : ℝ)) := by positivity
  have hC : ∀ m : ℕ, cNorm 0 (iteratedDeriv m Ψ) 0 (1 / (M : ℝ)) ≤
      m.factorial * (20 * (Q : ℝ) ^ 4) ^ m * (4 * s) := by
    intro m
    refine (cNorm_iteratedDeriv_div_le Q m f g hfq hgq (1 / (M : ℝ)) hb hg0).trans ?_
    have hp := pow_le_pow_left₀ hbase0 hbase m
    have h4 : 0 ≤ cNorm 0 Ψ 0 (1 / (M : ℝ)) := by
      rw [cNorm_zero_eq]; exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hΨ4 h4 (by positivity)
  have hpt : ∀ m : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) (1 / M),
      |iteratedDeriv m Ψ y| ≤ m.factorial * (20 * (Q : ℝ) ^ 4) ^ m * (4 * s) := by
    intro m y hy
    have := abs_le_cNorm_zero (iteratedDeriv m Ψ) 0 (1 / (M : ℝ))
      (by rw [iteratedDeriv_zero]; exact poly_div_continuousOn_iteratedDeriv f g _ hb hg0 _) y hy
    rw [iteratedDeriv_zero] at this
    exact this.trans (hC m)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / M) := ⟨le_rfl, hb.le⟩
  refine ⟨Ψ 0, iteratedDeriv 1 Ψ 0, ?_, ?_, ?_⟩
  · have := hpt 0 0 h0mem
    simpa using this
  · have := hpt 1 0 h0mem
    refine this.trans (le_of_eq ?_)
    simp; ring
  · intro N hMN
    have hNp : (0 : ℝ) < N := lt_of_lt_of_le hMp (by exact_mod_cast hMN)
    have hx : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hxM : 1 / (N : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hMp (by exact_mod_cast hMN)
    have hT := taylor_step Ψ (1 / (N : ℝ)) hx 1
      (fun y hy => poly_div_contDiffAt f g _ y (hg0 y ⟨hy.1, hy.2.trans hxM⟩))
      (3200 * (Q : ℝ) ^ 8 * s)
      (fun y hy => by
        have := hpt 2 y ⟨hy.1, hy.2.trans hxM⟩
        refine this.trans (le_of_eq ?_)
        simp [Nat.factorial]; ring)
    have hFN : F N = Ψ (1 / (N : ℝ)) := hF N hMN
    have e1 : F N - Ψ 0 - iteratedDeriv 1 Ψ 0 / N =
        Ψ (1 / (N : ℝ)) - ∑ k ∈ Finset.range (1 + 1),
          iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * (1 / (N : ℝ)) ^ k := by
      rw [hFN, Finset.sum_range_succ, Finset.sum_range_one]
      simp [Nat.factorial]; ring
    rw [e1]
    refine hT.trans (le_of_eq ?_)
    simp [Nat.factorial]; field_simp; ring

end BordenaveCollins.PartA
end

section
/-!
# Part A, module 2: the master inequality for polynomial test functions

For a sequence of positive functionals `E n` of mass at most one on `[-K, K]` whose polynomial
moments are rational in `1/n`, the limits `ν₀(h) = lim E n h`, `ν₁(h) = lim n (E n h - ν₀ h)`
exist, are linear in the polynomial `h`, and
`|E n h - ν₀ h - ν₁ h / n| ≤ A q⁸ sup_{[-K,K]} |h| / n²` for `deg h ≤ q`.
-/

open Polynomial Filter Topology StrongConv

namespace BordenaveCollins.PartA

/-- A sequence of positive functionals of mass at most one on `[-K, K]`. -/
structure PosFun (K : ℝ) (E : ℕ → (ℝ → ℝ) → ℝ) : Prop where
  hK : 0 < K
  hadd : ∀ n f g, E n (f + g) = E n f + E n g
  hsmul : ∀ n (a : ℝ) f, E n (a • f) = a * E n f
  hmono : ∀ n f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E n f ≤ E n g
  hone : ∀ n, E n (fun _ => 1) ≤ 1

namespace PosFun

variable {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ}

lemma zero (hE : PosFun K E) (n : ℕ) : E n 0 = 0 := by
  have := hE.hsmul n 0 0
  simpa using this

lemma sub (hE : PosFun K E) (n : ℕ) (f g : ℝ → ℝ) : E n (f - g) = E n f - E n g := by
  have : f - g = f + (-1 : ℝ) • g := by ext x; simp [sub_eq_add_neg]
  rw [this, hE.hadd, hE.hsmul]; ring

lemma one_nonneg (hE : PosFun K E) (n : ℕ) : 0 ≤ E n (fun _ => 1) := by
  have := hE.hmono n 0 (fun _ => 1) (fun x _ => by simp)
  rwa [hE.zero] at this

lemma abs_le (hE : PosFun K E) (n : ℕ) (f : ℝ → ℝ) (B : ℝ)
    (h : ∀ x ∈ Set.Icc (-K) K, |f x| ≤ B) : |E n f| ≤ B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (h 0 ⟨by linarith [hE.hK], hE.hK.le⟩)
  have h1 := hE.one_nonneg n
  have h2 := hE.hone n
  have hu := hE.hmono n f (B • fun _ => (1 : ℝ)) (fun x hx => by
    simpa using (_root_.abs_le.1 (h x hx)).2)
  have hl := hE.hmono n ((-B) • fun _ => (1 : ℝ)) f (fun x hx => by
    simpa using (_root_.abs_le.1 (h x hx)).1)
  rw [hE.hsmul] at hu hl
  rw [_root_.abs_le]
  constructor <;> nlinarith

lemma abs_sub_le (hE : PosFun K E) (n : ℕ) (f g : ℝ → ℝ) (B : ℝ)
    (h : ∀ x ∈ Set.Icc (-K) K, |f x - g x| ≤ B) : |E n f - E n g| ≤ B := by
  rw [← hE.sub]
  exact hE.abs_le n _ B h

/-- `E n` restricted to polynomials, as a linear map. -/
noncomputable def polyL (hE : PosFun K E) (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun h := E n (fun x => h.eval x)
  map_add' h g := by
    have : (fun x => (h + g).eval x) = (fun x => h.eval x) + (fun x => g.eval x) := by
      ext x; simp
    rw [this, hE.hadd]
  map_smul' a h := by
    have : (fun x => (a • h).eval x) = a • (fun x => h.eval x) := by
      ext x; simp
    rw [this, hE.hsmul]; rfl

lemma polyL_apply (hE : PosFun K E) (n : ℕ) (h : ℝ[X]) :
    hE.polyL n h = E n (fun x => h.eval x) := rfl

end PosFun

/-- The rationality hypothesis, normalized (`c = 1`). -/
def RatHyp (E : ℕ → (ℝ → ℝ) → ℝ) (C : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
    (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
    ∀ h : ℝ[X], h.natDegree ≤ q → ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
      ∀ n : ℕ, C * q ≤ n →
        E n (fun x => h.eval x) = f.eval (1 / (n : ℝ)) / gq.eval (1 / (n : ℝ))

lemma natDegree_comp_scale_le (p : ℝ[X]) (a : ℝ) :
    (p.comp (Polynomial.C a * X)).natDegree ≤ p.natDegree := by
  refine (natDegree_comp_le).trans ?_
  have h1 : (Polynomial.C a * X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  calc p.natDegree * (Polynomial.C a * X : ℝ[X]).natDegree ≤ p.natDegree * 1 :=
        Nat.mul_le_mul_left _ h1
    _ = p.natDegree := mul_one _

lemma rat_normalize (E : ℕ → (ℝ → ℝ) → ℝ) (c : ℕ) (hc : 1 ≤ c)
    (hrat : ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ n : ℕ, C * q ≤ n →
          E n (fun x => h.eval x) =
            f.eval (1 / ((c : ℝ) * n)) / gq.eval (1 / ((c : ℝ) * n))) :
    ∃ C : ℕ, 1 ≤ C ∧ RatHyp E C := by
  obtain ⟨C₀, h₀⟩ := hrat
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < c := by linarith
  refine ⟨C₀ + 1, by omega, fun q hq => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨gq, hgdeg, hgb, hh⟩ := h₀ q hq
  have hev : ∀ (p : ℝ[X]) (x : ℝ), (p.comp (Polynomial.C (1 / (c : ℝ)) * X)).eval x =
      p.eval (1 / (c : ℝ) * x) := by
    intro p x; simp [eval_comp]
  refine ⟨gq.comp (Polynomial.C (1 / (c : ℝ)) * X), ?_, ?_, ?_⟩
  · exact (natDegree_comp_scale_le _ _).trans (hgdeg.trans (Nat.mul_le_mul_right _ (by omega)))
  · intro x hx
    rw [hev]
    have hy0 : 0 ≤ 1 / (c : ℝ) * x := mul_nonneg (by positivity) hx.1
    have hyx : 1 / (c : ℝ) * x ≤ x := by
      have : 1 / (c : ℝ) ≤ 1 := by rw [div_le_one hcpos]; exact hc1
      nlinarith [hx.1]
    rcases Nat.eq_zero_or_pos C₀ with h0 | hpos
    · subst h0
      have hd : gq.natDegree ≤ 0 := by simpa using hgdeg
      have hconst : ∀ y : ℝ, gq.eval y = gq.eval 0 := by
        intro y
        rw [eq_C_of_natDegree_le_zero hd]; simp
      rw [hconst]
      exact hgb 0 ⟨le_rfl, by simp⟩
    · refine hgb _ ⟨hy0, hyx.trans (hx.2.trans ?_)⟩
      have hCp : (0 : ℝ) < C₀ := by exact_mod_cast hpos
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith [sq_nonneg (q : ℝ)]
  · intro h hdeg
    obtain ⟨f, hfdeg, hf⟩ := hh h hdeg
    refine ⟨f.comp (Polynomial.C (1 / (c : ℝ)) * X), ?_, ?_⟩
    · exact (natDegree_comp_scale_le _ _).trans (hfdeg.trans (Nat.mul_le_mul_right _ (by omega)))
    · intro n hn
      have hn' : C₀ * q ≤ n := le_trans (Nat.mul_le_mul_right _ (by omega)) hn
      rw [hf n hn', hev, hev]
      have : 1 / (c : ℝ) * (1 / (n : ℝ)) = 1 / ((c : ℝ) * n) := by
        rw [one_div_mul_one_div]
      rw [this]

lemma expansion_large {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ} (hE : PosFun K E) (C : ℕ) (hC : 1 ≤ C)
    (hR : RatHyp E C) (q : ℕ) (hq : 1 ≤ q) (h : ℝ[X]) (hh : h.natDegree ≤ q) (s : ℝ)
    (hs : ∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) :
    ∃ l0 l1 : ℝ, |l0| ≤ 4 * s ∧ |l1| ≤ 80 * ((C * q : ℕ) : ℝ) ^ 4 * s ∧
      ∀ n : ℕ, 2 * (C * q) ^ 2 ≤ n →
        |E n (fun x => h.eval x) - l0 - l1 / n| ≤
          1600 * ((C * q : ℕ) : ℝ) ^ 8 * s / (n : ℝ) ^ 2 := by
  obtain ⟨gq, hgdeg, hgb, hrest⟩ := hR q hq
  obtain ⟨f, hfdeg, hf⟩ := hrest h hh
  have hQ : 1 ≤ C * q := Nat.mul_pos hC hq
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine core_est (C * q) hQ f gq hfdeg hgdeg ?_ (fun n => E n (fun x => h.eval x)) s ?_ ?_
  · intro x hx
    refine hgb x ⟨hx.1, hx.2.trans ?_⟩
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    nlinarith [mul_pos (by linarith : (0 : ℝ) < C) (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]
  · intro n hn
    refine hf n (le_trans ?_ hn)
    nlinarith
  · intro n
    exact hE.abs_le n _ s hs

lemma tendsto_of_expansion (F : ℕ → ℝ) (l0 l1 B : ℝ) (M : ℕ)
    (h : ∀ n : ℕ, M ≤ n → |F n - l0 - l1 / n| ≤ B / (n : ℝ) ^ 2) :
    Tendsto F atTop (𝓝 l0) ∧ Tendsto (fun n : ℕ => (n : ℝ) * (F n - l0)) atTop (𝓝 l1) := by
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) * (F n - l0)) atTop (𝓝 l1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat B)
    filter_upwards [eventually_ge_atTop (max M 1)] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right M 1).trans hn
    have hnp : (0 : ℝ) < n := by linarith
    have := h n ((le_max_left M 1).trans hn)
    have e : (n : ℝ) * (F n - l0) - l1 = n * (F n - l0 - l1 / n) := by field_simp
    rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos hnp]
    calc (n : ℝ) * |F n - l0 - l1 / n| ≤ n * (B / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this hnp.le
      _ = B / n := by field_simp
  refine ⟨?_, h2⟩
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) * (F n - l0) * (1 / (n : ℝ)) + l0) atTop
      (𝓝 (l1 * 0 + l0)) :=
    (h2.mul tendsto_one_div_atTop_nhds_zero_nat).add tendsto_const_nhds
  rw [mul_zero, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  ring

/-- The master inequality for polynomials, with the limit functionals. -/
theorem poly_master {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ} (hE : PosFun K E) (C : ℕ) (hC : 1 ≤ C)
    (hR : RatHyp E C) :
    ∃ (ν₀ ν₁ : ℝ[X] →ₗ[ℝ] ℝ) (A : ℝ), 0 ≤ A ∧
      (∀ h : ℝ[X], Tendsto (fun n : ℕ => E n (fun x => h.eval x)) atTop (𝓝 (ν₀ h))) ∧
      (∀ h : ℝ[X], Tendsto (fun n : ℕ => (n : ℝ) * (E n (fun x => h.eval x) - ν₀ h)) atTop
        (𝓝 (ν₁ h))) ∧
      ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
        (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) →
          |ν₀ h| ≤ A * (q : ℝ) ^ 4 * s ∧ |ν₁ h| ≤ A * (q : ℝ) ^ 4 * s ∧
          ∀ n : ℕ, 1 ≤ n →
            |E n (fun x => h.eval x) - ν₀ h - ν₁ h / n| ≤ A * (q : ℝ) ^ 8 * s / (n : ℝ) ^ 2 := by
  have hbdd : ∀ h : ℝ[X], ∃ s : ℝ, ∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s := by
    intro h
    obtain ⟨s, hs⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun x => h.eval x)
      (s := Set.Icc (-K) K) h.continuous.continuousOn
    exact ⟨s, fun x hx => by simpa using hs x hx⟩
  have hex : ∀ h : ℝ[X], ∃ l0 l1 : ℝ,
      Tendsto (fun n : ℕ => E n (fun x => h.eval x)) atTop (𝓝 l0) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * (E n (fun x => h.eval x) - l0)) atTop (𝓝 l1) := by
    intro h
    obtain ⟨s, hs⟩ := hbdd h
    obtain ⟨l0, l1, -, -, hexp⟩ := expansion_large hE C hC hR (max h.natDegree 1)
      (le_max_right _ _) h (le_max_left _ _) s hs
    exact ⟨l0, l1, tendsto_of_expansion _ l0 l1 _ _ hexp⟩
  choose n0 n1 h0 h1 using hex
  have hL : ∀ (n : ℕ) (h : ℝ[X]), E n (fun x => h.eval x) = hE.polyL n h := fun n h => rfl
  have add0 : ∀ h g, n0 (h + g) = n0 h + n0 g := by
    intro h g
    refine tendsto_nhds_unique (h0 (h + g)) ?_
    have := (h0 h).add (h0 g)
    simp only [hL] at this ⊢
    simpa using this
  have smul0 : ∀ (a : ℝ) h, n0 (a • h) = a * n0 h := by
    intro a h
    refine tendsto_nhds_unique (h0 (a • h)) ?_
    have := (h0 h).const_mul a
    simp only [hL] at this ⊢
    simpa using this
  have add1 : ∀ h g, n1 (h + g) = n1 h + n1 g := by
    intro h g
    refine tendsto_nhds_unique (h1 (h + g)) ?_
    have := (h1 h).add (h1 g)
    simp only [hL] at this ⊢
    refine this.congr fun n => ?_
    rw [map_add, add0]; ring
  have smul1 : ∀ (a : ℝ) h, n1 (a • h) = a * n1 h := by
    intro a h
    refine tendsto_nhds_unique (h1 (a • h)) ?_
    have := (h1 h).const_mul a
    simp only [hL] at this ⊢
    refine this.congr fun n => ?_
    rw [map_smul, smul0, smul_eq_mul]; ring
  let ν₀ : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := n0, map_add' := add0, map_smul' := fun a h => by simpa using smul0 a h }
  let ν₁ : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := n1, map_add' := add1, map_smul' := fun a h => by simpa using smul1 a h }
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hC4 : (1 : ℝ) ≤ (C : ℝ) ^ 4 := one_le_pow₀ hC1
  refine ⟨ν₀, ν₁, 1600 * (C : ℝ) ^ 8, by positivity, h0, h1, ?_⟩
  intro q hq h hh s hs
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq4 : (1 : ℝ) ≤ (q : ℝ) ^ 4 := one_le_pow₀ hq1
  obtain ⟨l0, l1, hl0, hl1, hexp⟩ := expansion_large hE C hC hR q hq h hh s hs
  obtain ⟨t0, t1⟩ := tendsto_of_expansion _ l0 l1 _ _ hexp
  obtain rfl : l0 = n0 h := tendsto_nhds_unique t0 (h0 h)
  obtain rfl : l1 = n1 h := tendsto_nhds_unique t1 (h1 h)
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0 ⟨by linarith [hE.hK], hE.hK.le⟩)
  set Q : ℝ := ((C * q : ℕ) : ℝ) with hQdef
  have hQe : Q = (C : ℝ) * q := by rw [hQdef]; push_cast; ring
  have hQ1 : 1 ≤ Q := by rw [hQe]; nlinarith
  have hQ4 : 1 ≤ Q ^ 4 := one_le_pow₀ hQ1
  have hQ4e : Q ^ 4 = (C : ℝ) ^ 4 * (q : ℝ) ^ 4 := by rw [hQe]; ring
  have hQ8e : Q ^ 8 = (C : ℝ) ^ 8 * (q : ℝ) ^ 8 := by rw [hQe]; ring
  have hC8 : (C : ℝ) ^ 4 ≤ (C : ℝ) ^ 8 := pow_le_pow_right₀ hC1 (by norm_num)
  have hcq : (C : ℝ) ^ 4 * (q : ℝ) ^ 4 * s ≤ (C : ℝ) ^ 8 * (q : ℝ) ^ 4 * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC8 (by positivity)) hs0
  have hcq0 : 0 ≤ (C : ℝ) ^ 4 * (q : ℝ) ^ 4 * s := by positivity
  have hsle : s ≤ (C : ℝ) ^ 4 * (q : ℝ) ^ 4 * s := by
    have : 1 ≤ (C : ℝ) ^ 4 * (q : ℝ) ^ 4 := by nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · show |n0 h| ≤ _
    linarith
  · show |n1 h| ≤ _
    rw [hQ4e] at hl1
    linarith
  · intro n hn
    show |E n (fun x => h.eval x) - n0 h - n1 h / n| ≤ _
    rcases le_or_gt (2 * (C * q) ^ 2) n with hbig | hsmall
    · refine (hexp n hbig).trans (le_of_eq ?_)
      rw [hQ8e]; ring
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnp : (0 : ℝ) < n := by linarith
      have hnlt : (n : ℝ) ≤ 2 * Q ^ 2 := by
        have : ((n : ℕ) : ℝ) ≤ ((2 * (C * q) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsmall.le
        rw [hQdef]; push_cast at this ⊢; linarith
      have hn2 : (n : ℝ) ^ 2 ≤ 4 * Q ^ 4 := by
        have := pow_le_pow_left₀ hnp.le hnlt 2
        nlinarith
      have hE1 := hE.abs_le n _ s hs
      have hdiv : |n1 h / n| ≤ 80 * Q ^ 4 * s := by
        rw [abs_div, abs_of_pos hnp]
        refine (div_le_self (abs_nonneg _) hn1).trans hl1
      have hsQ : s ≤ Q ^ 4 * s := by nlinarith
      have h85 : |E n (fun x => h.eval x) - n0 h - n1 h / n| ≤ 85 * Q ^ 4 * s := by
        have a1 := abs_sub (E n (fun x => h.eval x) - n0 h) (n1 h / n)
        have a2 := abs_sub (E n (fun x => h.eval x)) (n0 h)
        linarith
      refine h85.trans ?_
      rw [le_div_iff₀ (by positivity),
        show 1600 * (C : ℝ) ^ 8 * (q : ℝ) ^ 8 * s = 1600 * Q ^ 8 * s by rw [hQ8e]; ring]
      have hQ4s : 0 ≤ Q ^ 4 * s := by positivity
      calc 85 * Q ^ 4 * s * (n : ℝ) ^ 2 ≤ 85 * Q ^ 4 * s * (4 * Q ^ 4) :=
            mul_le_mul_of_nonneg_left hn2 (by positivity)
        _ = 340 * (Q ^ 4 * s) * Q ^ 4 := by ring
        _ ≤ 1600 * (Q ^ 4 * s) * Q ^ 4 := by nlinarith [mul_nonneg hQ4s (by positivity : (0:ℝ) ≤ Q ^ 4)]
        _ = 1600 * Q ^ 8 * s := by ring

end BordenaveCollins.PartA
end

section
/-!
# Part A, module 3: Chebyshev expansions and polynomial approximation (real analysis)

Generic lemmas: `Tⱼ(x/K)` as polynomials, the Chebyshev expansion of a polynomial, simultaneous
polynomial approximation of a smooth function and its derivatives, and the stability of the
`L^β` norm of derivatives of `θ ↦ h(K cos θ)`.
-/

open Polynomial Filter Topology StrongConv

namespace BordenaveCollins.PartA

/-- `Tⱼ(x/K)` as a polynomial. -/
noncomputable def chebK (K : ℝ) (j : ℕ) : ℝ[X] := (Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)

lemma sum_range_succ_eq_add_Icc (f : ℕ → ℝ) (q : ℕ) :
    ∑ j ∈ Finset.range (q + 1), f j = f 0 + ∑ j ∈ Finset.Icc 1 q, f j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rfl

lemma natDegree_chebK_le (K : ℝ) (j : ℕ) : (chebK K j).natDegree ≤ j := by
  unfold chebK
  refine (natDegree_comp_le).trans ?_
  have h1 : (C K⁻¹ * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ?_
    simp
  simp only [Chebyshev.natDegree_T, Int.natAbs_natCast]
  nlinarith [h1]

lemma supOn_le_of_forall {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {c : ℝ}
    (h : ∀ x ∈ Set.Icc a b, |f x| ≤ c) : supOn f a b ≤ c := by
  unfold supOn
  apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma cNorm_le_of_abs_le (k : ℕ) (f : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ)
    (hf : ∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R, |iteratedDeriv r f x| ≤ ε) :
    cNorm k f (-R) R ≤ (k + 1) * ε := by
  unfold cNorm
  calc ∑ j ∈ Finset.range (k + 1), supOn (iteratedDeriv j f) (-R) R
      ≤ ∑ j ∈ Finset.range (k + 1), ε := by
        apply Finset.sum_le_sum
        intro j hj
        exact supOn_le_of_forall (by linarith) (hf j (by simp at hj; omega))
    _ = (k + 1) * ε := by simp

lemma iteratedDeriv_sub_of_contDiff (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (r : ℕ) :
    iteratedDeriv r (fun x => f x - g x) = fun x => iteratedDeriv r f x - iteratedDeriv r g x := by
  funext x
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  exact iteratedDeriv_fun_sub (hf.contDiffAt.of_le hr) (hg.contDiffAt.of_le hr)

lemma abs_iteratedDeriv_cos_le (i : ℕ) (θ : ℝ) : |iteratedDeriv i Real.cos θ| ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [Real.iteratedDeriv_even_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_cos_le_one θ
  · rw [Real.iteratedDeriv_odd_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_sin_le_one θ

lemma abs_iteratedDeriv_comp_cos_le (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ)
    (hK : 0 ≤ K) (r : ℕ) (ε : ℝ)
    (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K, |iteratedDeriv i g x| ≤ ε) (θ : ℝ) :
    |iteratedDeriv r (fun θ => g (K * Real.cos θ)) θ| ≤ (r.factorial : ℝ) * ε * (max K 1) ^ r := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun θ => K * Real.cos θ) := contDiff_const.mul Real.contDiff_cos
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hmem : K * Real.cos θ ∈ Set.Icc (-K) K := by
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    constructor <;> nlinarith
  have key := norm_iteratedFDeriv_comp_le (g := g) (f := fun θ => K * Real.cos θ) (n := r)
    hg hf hr θ (C := ε) (D := max K 1) ?_ ?_
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at key
    exact key
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hε i hi _ hmem
  · intro i hi1 _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg hK]
    calc K * |iteratedDeriv i Real.cos θ| ≤ K * 1 :=
          mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le i θ) hK
      _ ≤ max K 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max K 1 ^ i := le_self_pow₀ (le_max_right _ _) (by omega)

lemma lpNormCircle_le_add (β : ℝ) (hβ : 1 < β) (F G : ℝ → ℝ) (hF : Continuous F)
    (hG : Continuous G) (δ : ℝ) (hδ : ∀ θ, |F θ - G θ| ≤ δ) :
    lpNormCircle β F ≤ lpNormCircle β G + (2 * Real.pi + 1) * δ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  set μ := MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))
  set p := ENNReal.ofReal β
  have hp1 : 1 ≤ p := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hβ.le
  have hptr : p.toReal = β := ENNReal.toReal_ofReal (by linarith)
  have hμ : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    simp [μ, Real.volume_Icc]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hbound : ∀ (H : ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ x ∈ Set.Icc 0 (2 * Real.pi), ‖H x‖ ≤ C) →
      MeasureTheory.eLpNorm H p μ ≤ ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * C) := by
    intro H C hC hH
    refine (MeasureTheory.eLpNorm_le_of_ae_bound
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hH)).trans (le_of_eq ?_)
    rw [hμ, hptr, ENNReal.ofReal_rpow_of_nonneg hpi (by positivity), ← ENNReal.ofReal_mul
      (by positivity)]
  have hFG : MeasureTheory.eLpNorm (fun x => F x - G x) p μ ≤
      ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    hbound _ δ hδ0 (fun x _ => by rw [Real.norm_eq_abs]; exact hδ x)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := G)
    (s := Set.Icc 0 (2 * Real.pi)) hG.continuousOn
  have hGfin : MeasureTheory.eLpNorm G p μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hbound G (max M 0) (le_max_right _ _) (fun x hx => (hM x hx).trans (le_max_left _ _)))
  have htri : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + MeasureTheory.eLpNorm (fun x => F x - G x) p μ := by
    have := MeasureTheory.eLpNorm_add_le (μ := μ) (p := p) (f := G) (g := fun x => F x - G x)
      hG.aestronglyMeasurable (hF.sub hG).aestronglyMeasurable hp1
    convert this using 2
    funext x; simp
  have hsum : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    htri.trans (add_le_add_right hFG _)
  unfold lpNormCircle
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hGfin, ENNReal.ofReal_ne_top⟩) hsum
  rw [ENNReal.toReal_add hGfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h1
  refine h1.trans (add_le_add_right ?_ _)
  apply mul_le_mul_of_nonneg_right _ hδ0
  have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc (2 * Real.pi) ^ β⁻¹ ≤ (2 * Real.pi) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpi1 (inv_le_one_of_one_le₀ hβ.le)
    _ ≤ 2 * Real.pi + 1 := by rw [Real.rpow_one]; linarith

lemma natDegree_chebK (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).natDegree = j := by
  unfold chebK
  rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero hK.ne')]
  simp

lemma chebK_coeff_ne_zero (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).coeff j ≠ 0 := by
  have h := natDegree_chebK K hK j
  have hne : chebK K j ≠ 0 := by
    intro h0
    have h1 : (chebK K j).leadingCoeff ≠ 0 := by
      unfold chebK
      rw [leadingCoeff_comp (by rw [natDegree_C_mul_X _ (inv_ne_zero hK.ne')]; norm_num)]
      simp [hK.ne']
    rw [h0] at h1
    simp at h1
  have := leadingCoeff_ne_zero.mpr hne
  rwa [leadingCoeff, h] at this

lemma exists_chebyshev_expansion_aux (K : ℝ) (hK : 0 < K) (m : ℕ) :
    ∀ p : ℝ[X], p.natDegree ≤ m →
      ∃ a : ℕ → ℝ, p = ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
  induction m with
  | zero =>
    intro p hp
    refine ⟨fun _ => p.coeff 0, ?_⟩
    rw [eq_C_of_natDegree_le_zero hp]
    simp [chebK]
  | succ m ih =>
    intro p hp
    set c := p.coeff (m + 1) / (chebK K (m + 1)).coeff (m + 1)
    have hc : c * (chebK K (m + 1)).coeff (m + 1) = p.coeff (m + 1) :=
      div_mul_cancel₀ _ (chebK_coeff_ne_zero K hK (m + 1))
    have hdeg : (p - Polynomial.C c * chebK K (m + 1)).natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (m + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_chebK_le K (m + 1)) h)]
        simp
      · obtain rfl : N = m + 1 := by omega
        rw [hc]; simp
    obtain ⟨a, ha⟩ := ih _ hdeg
    refine ⟨fun j => if j = m + 1 then c else a j, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [if_true]
    have : ∑ j ∈ Finset.range (m + 1),
        Polynomial.C (if j = m + 1 then c else a j) * chebK K j =
        ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp at hj
      rw [if_neg (by omega)]
    rw [this, ← ha]
    ring

lemma exists_chebyshev_expansion (p : ℝ[X]) (K : ℝ) (hK : 0 < K) :
    ∃ a : ℕ → ℝ,
      (∀ x : ℝ, p.eval x = ∑ j ∈ Finset.range (p.natDegree + 1),
        a j * (Chebyshev.T ℝ j).eval (x / K)) ∧
      p = ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.C (a j) * chebK K j := by
  obtain ⟨a, ha⟩ := exists_chebyshev_expansion_aux K hK p.natDegree p le_rfl
  refine ⟨a, ?_, ha⟩
  intro x
  conv_lhs => rw [ha]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp [chebK, eval_comp, div_eq_inv_mul]

lemma exists_antiderivative (q : ℝ[X]) : ∃ Q : ℝ[X], derivative Q = q := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1),
    Polynomial.C (q.coeff i / ((i : ℝ) + 1)) * X ^ (i + 1), ?_⟩
  rw [derivative_sum]
  conv_rhs => rw [as_sum_range_C_mul_X_pow q]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_C_mul_X_pow]
  congr 2
  · push_cast
    field_simp

lemma exists_poly_approx (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : ℕ) (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R,
      |iteratedDeriv r h x - iteratedDeriv r (fun x => p.eval x) x| ≤ ε := by
  induction k generalizing h ε with
  | zero =>
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R h
      hh.continuous.continuousOn ε hε
    refine ⟨p, fun r hr x hx => ?_⟩
    obtain rfl : r = 0 := by omega
    simp only [iteratedDeriv_zero]
    rw [abs_sub_comm]
    exact (hp x hx).le
  | succ k ih =>
    rcases lt_or_ge R 0 with hR | hR
    · refine ⟨0, fun r _ x hx => ?_⟩
      exfalso
      have := hx.1.trans hx.2
      linarith
    have hR1 : 0 < 2 * R + 1 := by linarith
    set ε' := ε / (2 * R + 1) with hε'
    have hε'pos : 0 < ε' := div_pos hε hR1
    have hε'mul : ε' * (2 * R + 1) = ε := div_mul_cancel₀ _ hR1.ne'
    have hε'le : ε' ≤ ε := by nlinarith
    obtain ⟨hdiff, hd⟩ := contDiff_infty_iff_deriv.mp hh
    obtain ⟨q, hq⟩ := ih (deriv h) hd ε' hε'pos
    obtain ⟨Q, hQ⟩ := exists_antiderivative q
    set p := Q + Polynomial.C (h (-R) - Q.eval (-R)) with hpdef
    have hpd : derivative p = q := by
      rw [hpdef, derivative_add, derivative_C, add_zero, hQ]
    have hderiv : deriv (fun x => p.eval x) = fun x => q.eval x := by
      funext x
      rw [Polynomial.deriv, hpd]
    refine ⟨p, fun r hr x hx => ?_⟩
    rcases r with _ | s
    · simp only [iteratedDeriv_zero]
      have hg0 : h (-R) - p.eval (-R) = 0 := by
        rw [hpdef]; simp
      have hmem : (-R) ∈ Set.Icc (-R) R := ⟨le_rfl, by linarith⟩
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (f := fun y => h y - p.eval y) (s := Set.Icc (-R) R) (C := ε')
        (fun y _ => (hdiff y).sub p.differentiableAt) ?_ (convex_Icc _ _) hmem hx
      · simp only [hg0, sub_zero, Real.norm_eq_abs] at hmvt
        have hxR : |x - -R| ≤ 2 * R := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        calc |h x - eval x p| ≤ ε' * |x - -R| := hmvt
          _ ≤ ε' * (2 * R) := mul_le_mul_of_nonneg_left hxR hε'pos.le
          _ ≤ ε := by nlinarith
      · intro y hy
        rw [deriv_fun_sub (hdiff y) p.differentiableAt, Polynomial.deriv, hpd, Real.norm_eq_abs]
        have := hq 0 (Nat.zero_le _) y hy
        simpa only [iteratedDeriv_zero] using this
    · rw [iteratedDeriv_succ', iteratedDeriv_succ', hderiv]
      exact (hq s (by omega) x hx).trans hε'le

lemma lpNormCircle_nonneg (β : ℝ) (F : ℝ → ℝ) : 0 ≤ lpNormCircle β F :=
  ENNReal.toReal_nonneg

lemma conjExp_pos (β : ℝ) (hβ : 1 < β) : 0 < conjExp β := by
  unfold conjExp
  have : 1 / β < 1 := by rw [div_lt_one (by linarith)]; exact hβ
  exact inv_pos.mpr (by linarith)

/-! ## Assembly -/
/-- The constant of Lemma 4.4. -/
noncomputable def Czyg : ℝ := Classical.choose abs_coeff_zero_le_and_sum_le_lpNormCircle

lemma Czyg_spec : ∀ (q : ℕ) (a : ℕ → ℝ) (K : ℝ), 0 < K →
      |a 0| ≤ cNorm 0 (fun x => ∑ j ∈ Finset.range (q + 1),
          a j * (Chebyshev.T ℝ j).eval (x / K)) (-K) K ∧
      ∀ (m : ℕ) (β : ℝ), 1 < β →
        ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤
          Czyg * conjExp β * lpNormCircle β (iteratedDeriv (m + 1) (fun θ =>
            ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))) :=
  Classical.choose_spec abs_coeff_zero_le_and_sum_le_lpNormCircle
lemma smooth_coe (h : smoothFun) : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ) := h.2

lemma poly_smooth (p : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (fun x => p.eval x) := (polyFun p).2

/-- The `L^β` side passes to the limit: a polynomial close to `h` in `C^(r)[-K, K]`. -/
lemma lp_perturb (h : smoothFun) (p : ℝ[X]) (K : ℝ) (hK : 0 ≤ K) (r : ℕ) (β : ℝ) (hβ : 1 < β)
    (ε : ℝ) (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K,
      |iteratedDeriv i (fun x => (h : ℝ → ℝ) x - p.eval x) x| ≤ ε) :
    lpNormCircle β (iteratedDeriv r (fun θ => p.eval (K * Real.cos θ))) ≤
      lpNormCircle β (iteratedDeriv r (fun θ => (h : ℝ → ℝ) (K * Real.cos θ))) +
        (2 * Real.pi + 1) * ((r.factorial : ℝ) * ε * (max K 1) ^ r) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => K * Real.cos θ) :=
    contDiff_const.mul Real.contDiff_cos
  have hhc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) :=
    (smooth_coe h).comp hc
  have hpc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => p.eval (K * Real.cos θ)) := (poly_smooth p).comp hc
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => (h : ℝ → ℝ) x - p.eval x) :=
    (smooth_coe h).sub (poly_smooth p)
  refine lpNormCircle_le_add β hβ _ _ (hpc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top))
    (hhc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)) _ fun θ => ?_
  have h1 := abs_iteratedDeriv_comp_cos_le _ hg K hK r ε hε θ
  have h2 := iteratedDeriv_sub_of_contDiff _ _ hhc hpc r
  have h3 : (fun θ => (fun x => (h : ℝ → ℝ) x - p.eval x) (K * Real.cos θ)) =
      fun θ => (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) θ - (fun θ => p.eval (K * Real.cos θ)) θ :=
    rfl
  rw [h3, h2] at h1
  rw [abs_sub_comm]
  exact h1
lemma abs_chebK_le (K : ℝ) (hK : 0 < K) (j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-K) K) :
    |(chebK K j).eval x| ≤ 1 := by
  simp only [chebK, eval_comp, eval_mul, eval_C, eval_X]
  apply Chebyshev.abs_eval_T_real_le_one
  rw [abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
  exact abs_le.mpr ⟨hx.1, hx.2⟩

end BordenaveCollins.PartA
end

section
/-!
# Part A, module 4: the master inequality for smooth test functions

From the polynomial master inequality (error `A q⁸ sup|h| / n²` in degree `q`) to smooth `h`:
Chebyshev expansion and Zygmund's bound for polynomials, then approximation of `h` and its
derivatives by polynomials; the functionals `ν₀, ν₁` are replaced by compactly supported
distributions extending them.
-/

open Polynomial Filter Topology StrongConv

namespace BordenaveCollins.PartA

/-- The master inequality for a polynomial, in terms of the derivatives of `p(K cos θ)`. -/
theorem cheb_master {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ} (hE : PosFun K E) (ν₀ ν₁ : ℝ[X] →ₗ[ℝ] ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hPM : ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
      (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) → ∀ n : ℕ, 1 ≤ n →
        |E n (fun x => h.eval x) - ν₀ h - ν₁ h / n| ≤ A * (q : ℝ) ^ 8 * s / (n : ℝ) ^ 2)
    (p : ℝ[X]) (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (hβ : 1 < β) :
    |E n (fun x => p.eval x) - ν₀ p - ν₁ p / n| ≤
      A / (n : ℝ) ^ 2 * (cNorm 0 (fun x => p.eval x) (-K) K + max Czyg 0 * conjExp β *
        lpNormCircle β (iteratedDeriv 9 (fun θ => p.eval (K * Real.cos θ)))) := by
  have hK := hE.hK
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨a, ha_eval, ha_poly⟩ := exists_chebyshev_expansion p K hK
  set q := p.natDegree with hq
  let err : ℝ[X] →ₗ[ℝ] ℝ := hE.polyL n - ν₀ - (1 / (n : ℝ)) • ν₁
  have herr : ∀ h : ℝ[X], err h = E n (fun x => h.eval x) - ν₀ h - ν₁ h / n := by
    intro h
    simp only [err, LinearMap.sub_apply, LinearMap.smul_apply, PosFun.polyL_apply, smul_eq_mul]
    ring
  have key : err p = ∑ j ∈ Finset.range (q + 1), a j * err (chebK K j) := by
    conv_lhs => rw [ha_poly]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  set B : ℝ := A / (n : ℝ) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hE0 : |err (chebK K 0)| ≤ B := by
    rw [herr]
    have := hPM 1 le_rfl (chebK K 0) ((natDegree_chebK_le K 0).trans zero_le_one) 1
      (abs_chebK_le K hK 0) n hn
    refine this.trans (le_of_eq ?_)
    rw [hB]; simp
  have hEj : ∀ j ∈ Finset.Icc 1 q, |a j * err (chebK K j)| ≤ B * ((j : ℝ) ^ 8 * |a j|) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have := hPM j hj1 (chebK K j) (natDegree_chebK_le K j) 1 (abs_chebK_le K hK j) n hn
    rw [← herr] at this
    rw [abs_mul]
    calc |a j| * |err (chebK K j)| ≤ |a j| * (A * (j : ℝ) ^ 8 * 1 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = B * ((j : ℝ) ^ 8 * |a j|) := by rw [hB]; ring
  obtain ⟨hz0, hzyg⟩ := Czyg_spec q a K hK
  have hfun : (fun θ => ∑ j ∈ Finset.range (q + 1),
      a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K)) = fun θ => p.eval (K * Real.cos θ) := by
    funext θ; rw [ha_eval]
  have hfun0 : (fun x => ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (x / K)) =
      fun x => p.eval x := by
    funext x; rw [ha_eval]
  rw [hfun0] at hz0
  have hZ := hzyg 8 β hβ
  rw [hfun] at hZ
  set lp := lpNormCircle β (iteratedDeriv 9 (fun θ => p.eval (K * Real.cos θ))) with hlp
  have hlp0 : 0 ≤ lp := lpNormCircle_nonneg _ _
  have hβs := conjExp_pos β hβ
  have hZ' : ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ 8 * |a j| ≤ max Czyg 0 * conjExp β * lp := by
    refine hZ.trans ?_
    have : 0 ≤ conjExp β * lp := by positivity
    calc Czyg * conjExp β * lp = Czyg * (conjExp β * lp) := by ring
      _ ≤ max Czyg 0 * (conjExp β * lp) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  rw [← herr, key, sum_range_succ_eq_add_Icc]
  have h0 : |a 0 * err (chebK K 0)| ≤ B * cNorm 0 (fun x => p.eval x) (-K) K := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul hE0 hz0 (abs_nonneg _) hB0
  have hsum : |∑ j ∈ Finset.Icc 1 q, a j * err (chebK K j)| ≤
      B * (max Czyg 0 * conjExp β * lp) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hEj).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hZ' hB0
  calc |a 0 * err (chebK K 0) + ∑ j ∈ Finset.Icc 1 q, a j * err (chebK K j)|
      ≤ |a 0 * err (chebK K 0)| + |∑ j ∈ Finset.Icc 1 q, a j * err (chebK K j)| :=
        abs_add_le _ _
    _ ≤ _ := by rw [mul_add]; linarith

/-- The master inequality for smooth test functions: an `O(n⁻²)` expansion. -/
theorem smooth_master {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ} (hE : PosFun K E) (ν₀ ν₁ : ℝ[X] →ₗ[ℝ] ℝ)
    (A : ℝ) (hA : 0 ≤ A)
    (hPM : ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
      (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) → ∀ n : ℕ, 1 ≤ n →
        |E n (fun x => h.eval x) - ν₀ h - ν₁ h / n| ≤ A * (q : ℝ) ^ 8 * s / (n : ℝ) ^ 2)
    (μ₀ μ₁ : smoothFun →ₗ[ℝ] ℝ) (hμ₀ : IsCSDistribution μ₀) (hμ₁ : IsCSDistribution μ₁)
    (h₀ : ∀ h : ℝ[X], μ₀ (polyFun h) = ν₀ h) (h₁ : ∀ h : ℝ[X], μ₁ (polyFun h) = ν₁ h)
    (h : smoothFun) :
    ∃ W : ℝ, ∀ n : ℕ, 1 ≤ n → |E n (h : ℝ → ℝ) - μ₀ h - μ₁ h / n| ≤ W / (n : ℝ) ^ 2 := by
  have hK := hE.hK
  obtain ⟨c₀, K₀, k₀, hc₀, hK₀, hck₀⟩ := hμ₀
  obtain ⟨c₁, K₁, k₁, hc₁, hK₁, hck₁⟩ := hμ₁
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := (h : ℝ → ℝ))
    (s := Set.Icc (-K) K) (smooth_coe h).continuous.continuousOn
  set Cz : ℝ := max Czyg 0 * conjExp 2 with hCz
  have hCz0 : 0 ≤ Cz := by
    have := conjExp_pos 2 (by norm_num)
    have := le_max_right Czyg 0
    positivity
  set lph := lpNormCircle 2 (iteratedDeriv 9 (fun θ => (h : ℝ → ℝ) (K * Real.cos θ))) with hlph
  refine ⟨A * (S + Cz * lph), fun n hn => ?_⟩
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  set R := K + K₀ + K₁ with hR
  set kk := 9 + k₀ + k₁ with hkk
  set B : ℝ := A / (n : ℝ) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set G : ℝ := (2 * Real.pi + 1) * (((9 : ℕ).factorial : ℝ) * (max K 1) ^ 9) with hG
  have hG0 : 0 ≤ G := by
    have : (0 : ℝ) ≤ max K 1 := le_trans zero_le_one (le_max_right _ _)
    have := Real.pi_pos
    positivity
  set M : ℝ := B * (1 + Cz * G) + 1 + c₀ * ((k₀ : ℝ) + 1) + c₁ * ((k₁ : ℝ) + 1) / n with hM
  have hM0 : 0 < M := by
    have : 0 ≤ B * (1 + Cz * G) := by positivity
    have : 0 ≤ c₀ * ((k₀ : ℝ) + 1) := by positivity
    have : 0 ≤ c₁ * ((k₁ : ℝ) + 1) / n := by positivity
    linarith
  have main : ∀ ε > 0, |E n (h : ℝ → ℝ) - μ₀ h - μ₁ h / n| ≤ B * (S + Cz * lph) + ε * M := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_poly_approx (h : ℝ → ℝ) (smooth_coe h) kk R ε hε
    set g : ℝ → ℝ := fun x => (h : ℝ → ℝ) x - p.eval x with hgdef
    have hg : ∀ r ≤ kk, ∀ x ∈ Set.Icc (-R) R, |iteratedDeriv r g x| ≤ ε := by
      intro r hr x hx
      rw [hgdef, iteratedDeriv_sub_of_contDiff _ _ (smooth_coe h) (poly_smooth p) r]
      exact hp r hr x hx
    have hsubK : ∀ x ∈ Set.Icc (-K) K, x ∈ Set.Icc (-R) R := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hg0 : ∀ x ∈ Set.Icc (-K) K, |(h : ℝ → ℝ) x - p.eval x| ≤ ε := by
      intro x hx
      have := hg 0 (Nat.zero_le _) x (hsubK x hx)
      simpa [hgdef] using this
    -- (a) the functional side
    have ha : |E n (h : ℝ → ℝ) - E n (fun x => p.eval x)| ≤ ε :=
      hE.abs_sub_le n _ _ ε hg0
    -- (b) the distributions
    have e2 : ((h - polyFun p : smoothFun) : ℝ → ℝ) = g := rfl
    have hb₀ : |μ₀ h - ν₀ p| ≤ c₀ * (((k₀ : ℝ) + 1) * ε) := by
      have e1 : μ₀ h - ν₀ p = μ₀ (h - polyFun p) := by rw [map_sub, h₀ p]
      rw [e1]
      refine (hck₀ _).trans (mul_le_mul_of_nonneg_left ?_ hc₀.le)
      rw [e2]
      exact cNorm_le_of_abs_le k₀ g K₀ hK₀.le ε fun r hr x hx =>
        hg r (by omega) x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hb₁ : |μ₁ h - ν₁ p| ≤ c₁ * (((k₁ : ℝ) + 1) * ε) := by
      have e1 : μ₁ h - ν₁ p = μ₁ (h - polyFun p) := by rw [map_sub, h₁ p]
      rw [e1]
      refine (hck₁ _).trans (mul_le_mul_of_nonneg_left ?_ hc₁.le)
      rw [e2]
      exact cNorm_le_of_abs_le k₁ g K₁ hK₁.le ε fun r hr x hx =>
        hg r (by omega) x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    -- (c) the polynomial master inequality
    have hc := cheb_master hE ν₀ ν₁ A hA hPM p n hn 2 (by norm_num)
    have hlp := lp_perturb h p K hK.le 9 2 (by norm_num) ε fun i hi x hx =>
      hg i (by omega) x (hsubK x hx)
    have hsup : cNorm 0 (fun x => p.eval x) (-K) K ≤ S + ε := by
      unfold cNorm
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, iteratedDeriv_zero]
      apply supOn_le_of_forall (by linarith)
      intro x hx
      have h1 := hS x hx
      have h2 := hg0 x hx
      rw [Real.norm_eq_abs] at h1
      have h3 : |p.eval x| ≤ |(h : ℝ → ℝ) x| + |(h : ℝ → ℝ) x - p.eval x| := by
        have := abs_sub_abs_le_abs_sub (p.eval x) ((h : ℝ → ℝ) x)
        rw [abs_sub_comm] at this
        linarith
      linarith
    have hc' : |E n (fun x => p.eval x) - ν₀ p - ν₁ p / n| ≤
        B * (S + Cz * lph) + ε * (B * (1 + Cz * G)) := by
      refine hc.trans ?_
      rw [← hB]
      have hin : cNorm 0 (fun x => p.eval x) (-K) K + max Czyg 0 * conjExp 2 *
          lpNormCircle 2 (iteratedDeriv 9 (fun θ => p.eval (K * Real.cos θ))) ≤
          (S + ε) + Cz * (lph + (2 * Real.pi + 1) * (((9 : ℕ).factorial : ℝ) * ε *
            (max K 1) ^ 9)) :=
        add_le_add hsup (mul_le_mul_of_nonneg_left hlp hCz0)
      refine (mul_le_mul_of_nonneg_left hin hB0).trans (le_of_eq ?_)
      rw [hG]; ring
    have hsplit : E n (h : ℝ → ℝ) - μ₀ h - μ₁ h / n =
        (E n (fun x => p.eval x) - ν₀ p - ν₁ p / n) +
        (E n (h : ℝ → ℝ) - E n (fun x => p.eval x)) - (μ₀ h - ν₀ p) - (μ₁ h - ν₁ p) / n := by
      ring
    have hb₁' : |(μ₁ h - ν₁ p) / n| ≤ ε * (c₁ * ((k₁ : ℝ) + 1) / n) := by
      rw [abs_div, abs_of_pos hnp]
      rw [show ε * (c₁ * ((k₁ : ℝ) + 1) / n) = c₁ * (((k₁ : ℝ) + 1) * ε) / n by ring]
      exact div_le_div_of_nonneg_right hb₁ hnp.le
    rw [hsplit]
    have t1 := abs_sub ((E n (fun x => p.eval x) - ν₀ p - ν₁ p / n) +
        (E n (h : ℝ → ℝ) - E n (fun x => p.eval x)) - (μ₀ h - ν₀ p)) ((μ₁ h - ν₁ p) / n)
    have t2 := abs_sub ((E n (fun x => p.eval x) - ν₀ p - ν₁ p / n) +
        (E n (h : ℝ → ℝ) - E n (fun x => p.eval x))) (μ₀ h - ν₀ p)
    have t3 := abs_add_le (E n (fun x => p.eval x) - ν₀ p - ν₁ p / n)
        (E n (h : ℝ → ℝ) - E n (fun x => p.eval x))
    have : ε * M = ε * (B * (1 + Cz * G)) + ε + c₀ * (((k₀ : ℝ) + 1) * ε) +
        ε * (c₁ * ((k₁ : ℝ) + 1) / n) := by rw [hM]; ring
    linarith
  have hfin : |E n (h : ℝ → ℝ) - μ₀ h - μ₁ h / n| ≤ B * (S + Cz * lph) := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := main (δ / M) (div_pos hδ hM0)
    rwa [div_mul_cancel₀ δ hM0.ne'] at this
  refine hfin.trans (le_of_eq ?_)
  rw [hB]; ring

end BordenaveCollins.PartA
end

section
/-!
# Part A: the abstract polynomial method (`abstract_tail`)

Assembly: the polynomial master inequality (`poly_master`), extension of `ν₀, ν₁` to compactly
supported distributions (CGTvH Lemma 4.7), their supports from the moment growth (Lemma 4.9),
and the smooth master inequality (`smooth_master`) applied to a test function vanishing near
`[-ρ, ρ]` and equal to one on `|x| ≥ ρ + ε`.
-/

open Polynomial Filter Topology StrongConv

namespace BordenaveCollins.PartA

/-- Moment growth `|u p| ≤ C (ρ + δ)^p` for all `δ > 0` bounds the limsup of `|u p|^(1/p)`. -/
lemma limsup_rpow_le (u : ℕ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |u p| ≤ C * (ρ + δ) ^ p) (η : ℝ) (hη : 0 < η) :
    limsup (fun p : ℕ => |u p| ^ (1 / (p : ℝ))) atTop ≤ ρ + η := by
  set δ : ℝ := min 1 (η / (ρ + 2)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ * (ρ + 2) ≤ η := by
    have : δ ≤ η / (ρ + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by linarith)] at this
  obtain ⟨C, hC⟩ := hu δ hδ0
  set C' : ℝ := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := by linarith
  have hlim : Tendsto (fun p : ℕ => C' ^ (1 / (p : ℝ))) atTop (𝓝 1) := by
    have : Tendsto ((fun x : ℝ => C' ^ x) ∘ fun n : ℕ => 1 / (n : ℝ)) atTop
        (𝓝 (C' ^ (0 : ℝ))) :=
      (Real.continuousAt_const_rpow (b := 0) hC'pos.ne').tendsto.comp
        tendsto_one_div_atTop_nhds_zero_nat
    rw [Real.rpow_zero] at this
    exact this
  have hev : ∀ᶠ p : ℕ in atTop, C' ^ (1 / (p : ℝ)) < 1 + δ :=
    (tendsto_order.1 hlim).2 (1 + δ) (by linarith)
  refine limsup_le_of_le ?_ ?_
  · exact (isBoundedUnder_of ⟨0, fun p => Real.rpow_nonneg (abs_nonneg _) _⟩).isCoboundedUnder_le
  · filter_upwards [hev, eventually_ge_atTop 1] with p hp hp1
    have hp0 : p ≠ 0 := by omega
    have hρδ : 0 ≤ ρ + δ := by linarith
    have h1 : |u p| ≤ C' * (ρ + δ) ^ p :=
      (hC p).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρδ p))
    have hexp : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    calc |u p| ^ (1 / (p : ℝ)) ≤ (C' * (ρ + δ) ^ p) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (abs_nonneg _) h1 hexp
      _ = C' ^ (1 / (p : ℝ)) * (ρ + δ) := by
          rw [Real.mul_rpow hC'pos.le (pow_nonneg hρδ p), one_div,
            Real.pow_rpow_inv_natCast hρδ hp0]
      _ ≤ (1 + δ) * (ρ + δ) := mul_le_mul_of_nonneg_right hp.le hρδ
      _ ≤ ρ + η := by nlinarith

/-- A compactly supported distribution with moment growth `(ρ + δ)^p` kills smooth functions
vanishing on `|x| ≤ ρ + ε/2`. -/
lemma csd_eq_zero (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |μ (polyFun (X ^ p))| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) (χ : smoothFun)
    (hχ : ∀ x : ℝ, |x| ≤ ρ + ε / 2 → (χ : ℝ → ℝ) x = 0) : μ χ = 0 := by
  have hL := limsup_rpow_le (fun p => μ (polyFun (X ^ p))) ρ hρ hu (ε / 4) (by positivity)
  have hsupp := supp_subset_Icc_limsup μ hμ
  refine vanishesNear_supp μ hμ χ ?_
  have hopen : IsOpen {x : ℝ | |x| < ρ + ε / 2} := isOpen_lt continuous_abs continuous_const
  have hsub : supp μ ⊆ {x : ℝ | |x| < ρ + ε / 2} := by
    intro x hx
    have := hsupp hx
    show |x| < ρ + ε / 2
    rw [abs_lt]
    constructor <;> linarith [this.1, this.2]
  exact Filter.eventually_of_mem (hopen.mem_nhdsSet.2 hsub) fun x hx => hχ x (le_of_lt hx)

/-- Extension of a functional on polynomials with a Markov-type bound to a compactly supported
distribution. -/
lemma exists_csExt (K : ℝ) (hK : 0 < K) (ν : ℝ[X] →ₗ[ℝ] ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hν : ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
      (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) → |ν h| ≤ A * (q : ℝ) ^ 4 * s) :
    ∃ μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = ν h := by
  have h1 : ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X],
      h.natDegree ≤ q → |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K := by
    refine ⟨A, ((4 : ℕ) : ℝ), K, hA, by positivity, hK.le, fun q hq h hh => ?_⟩
    rw [Real.rpow_natCast]
    refine hν q hq h hh _ fun x hx => ?_
    have := abs_le_cNorm_zero (fun x => h.eval x) (-K) K
      (by rw [iteratedDeriv_zero]; exact h.continuous.continuousOn) x hx
    rwa [iteratedDeriv_zero] at this
  obtain ⟨μ, hμ, -⟩ := ((tfae_extends_csDistribution ν).out 0 2).mp h1
  exact ⟨μ, hμ.1, hμ.2⟩

/-- A smooth test function with values in `[0, 1]`, zero on `|x| ≤ r₁`, one on `|x| ≥ r₂`. -/
lemma exists_cutoff (r₁ r₂ : ℝ) (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) :
    ∃ χ : smoothFun, (∀ x, 0 ≤ (χ : ℝ → ℝ) x) ∧ (∀ x, (χ : ℝ → ℝ) x ≤ 1) ∧
      (∀ x, |x| ≤ r₁ → (χ : ℝ → ℝ) x = 0) ∧ (∀ x, r₂ ≤ |x| → (χ : ℝ → ℝ) x = 1) := by
  have hd : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  refine ⟨⟨fun x => Real.smoothTransition ((x ^ 2 - r₁ ^ 2) / (r₂ ^ 2 - r₁ ^ 2)), ?_⟩,
    fun x => Real.smoothTransition.nonneg _, fun x => Real.smoothTransition.le_one _, ?_, ?_⟩
  · show ContDiff ℝ (⊤ : ℕ∞) _
    exact Real.smoothTransition.contDiff.comp
      (((contDiff_id.pow 2).sub contDiff_const).div_const _)
  · intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    have : x ^ 2 ≤ r₁ ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    have : r₂ ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (by linarith) hx 2
    rw [le_div_iff₀ hd]; linarith

theorem abstract_tail (K : ℝ) (hK : 0 < K) (c : ℕ) (hc : 1 ≤ c) (E : ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ n f g, E n (f + g) = E n f + E n g)
    (hsmul : ∀ n (a : ℝ) f, E n (a • f) = a * E n f)
    (hmono : ∀ n f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E n f ≤ E n g)
    (hone : ∀ n, E n (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ n : ℕ, C * q ≤ n →
          E n (fun x => h.eval x) =
            f.eval (1 / ((c : ℝ) * n)) / gq.eval (1 / ((c : ℝ) * n)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : ℕ → ℝ)
    (ha : ∀ p : ℕ, Tendsto (fun n : ℕ => E n (fun x => x ^ p)) atTop (𝓝 (a p)))
    (hb : ∀ p : ℕ, Tendsto (fun n : ℕ => ((c : ℝ) * n) * (E n (fun x => x ^ p) - a p)) atTop
      (𝓝 (b p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hbgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |b p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      E n (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤ C / (n : ℝ) ^ 2 := by
  have hE : PosFun K E := ⟨hK, hadd, hsmul, hmono, hone⟩
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < c := by linarith
  obtain ⟨C, hC, hR⟩ := rat_normalize E c hc hrat
  obtain ⟨ν₀, ν₁, A, hA, t0, t1, hbd⟩ := poly_master hE C hC hR
  have hXp : ∀ p : ℕ, (fun x : ℝ => (X ^ p : ℝ[X]).eval x) = fun x => x ^ p := by
    intro p; funext x; simp
  have hν₀ : ∀ p : ℕ, ν₀ (X ^ p) = a p := by
    intro p
    have := t0 (X ^ p)
    rw [hXp] at this
    exact tendsto_nhds_unique this (ha p)
  have hν₁ : ∀ p : ℕ, ν₁ (X ^ p) = b p / c := by
    intro p
    have h1 := t1 (X ^ p)
    rw [hXp, hν₀] at h1
    refine tendsto_nhds_unique h1 (((hb p).div_const (c : ℝ)).congr fun n => ?_)
    field_simp
  obtain ⟨μ₀, hμ₀, e₀⟩ := exists_csExt K hK ν₀ A hA
    (fun q hq h hh s hs => (hbd q hq h hh s hs).1)
  obtain ⟨μ₁, hμ₁, e₁⟩ := exists_csExt K hK ν₁ A hA
    (fun q hq h hh s hs => (hbd q hq h hh s hs).2.1)
  obtain ⟨χ, hχ0, hχ1, hχz, hχo⟩ := exists_cutoff (ρ + ε / 2) (ρ + ε) (by linarith) (by linarith)
  have z₀ : μ₀ χ = 0 := by
    refine csd_eq_zero μ₀ hμ₀ ρ hρ (fun δ hδ => ?_) ε hε χ hχz
    obtain ⟨C₀, hC₀⟩ := hagrow δ hδ
    exact ⟨C₀, fun p => by rw [e₀, hν₀]; exact hC₀ p⟩
  have z₁ : μ₁ χ = 0 := by
    refine csd_eq_zero μ₁ hμ₁ ρ hρ (fun δ hδ => ?_) ε hε χ hχz
    obtain ⟨C₁, hC₁⟩ := hbgrow δ hδ
    refine ⟨C₁, fun p => ?_⟩
    rw [e₁, hν₁, abs_div, abs_of_pos hcpos]
    exact (div_le_self (abs_nonneg _) hc1).trans (hC₁ p)
  obtain ⟨W, hW⟩ := smooth_master hE ν₀ ν₁ A hA
    (fun q hq h hh s hs => (hbd q hq h hh s hs).2.2) μ₀ μ₁ hμ₀ hμ₁ e₀ e₁ χ
  refine ⟨W, fun n hn => ?_⟩
  have h1 := hW n hn
  rw [z₀, z₁, zero_div, sub_zero, sub_zero] at h1
  have h2 : E n (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤ E n (χ : ℝ → ℝ) := by
    refine hmono n _ _ fun x _ => ?_
    by_cases hx : ρ + ε ≤ |x|
    · simp only [hx, if_true]; exact (hχo x hx).ge
    · simp only [hx, if_false]; exact hχ0 x
  exact h2.trans ((le_abs_self _).trans h1)

end BordenaveCollins.PartA
end

section
open Filter Topology Polynomial
open BordenaveCollins

theorem solution (K : ℝ) (hK : 0 < K) (c : ℕ) (hc : 1 ≤ c)
    (E : ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ n f g, E n (f + g) = E n f + E n g)
    (hsmul : ∀ n (a : ℝ) f, E n (a • f) = a * E n f)
    (hmono : ∀ n f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E n f ≤ E n g)
    (hone : ∀ n, E n (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ n : ℕ, C * q ≤ n →
          E n (fun x => h.eval x) =
            f.eval (1 / ((c : ℝ) * n)) / gq.eval (1 / ((c : ℝ) * n)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : ℕ → ℝ)
    (ha : ∀ p : ℕ, Tendsto (fun n : ℕ => E n (fun x => x ^ p)) atTop (𝓝 (a p)))
    (hb : ∀ p : ℕ, Tendsto (fun n : ℕ => ((c : ℝ) * n) * (E n (fun x => x ^ p) - a p)) atTop
      (𝓝 (b p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hbgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |b p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      E n (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤ C / (n : ℝ) ^ 2 :=
  BordenaveCollins.PartA.abstract_tail K hK c hc E hadd hsmul hmono hone hrat ρ hρ a b ha hb hagrow hbgrow ε hε

end
