-- Prove2me | solution 1 for BellmanDP.Variational.euler_error_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:04:10.940615+00:00
-- url     : https://prove2.me/submissions/e53b4038-78aa-4a16-b10c-068bfe314a99

import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation



namespace BellmanDP.Variational

open Set MeasureTheory

lemma ee_lip (G : ℝ → ℝ → ℝ) (m M : ℝ) (K : NNReal)
    (hG : LipschitzOnWith K (fun z : ℝ × ℝ => G z.1 z.2) (Icc m M ×ˢ Icc (0 : ℝ) 1))
    {a b u : ℝ} (ha : a ∈ Icc m M) (hb : b ∈ Icc m M) (hu : u ∈ Icc (0:ℝ) 1) :
    |G a u - G b u| ≤ K * |a - b| := by
  have := hG.dist_le_mul (x := (a,u)) (y := (b,u)) ⟨ha, hu⟩ ⟨hb, hu⟩
  simpa [Prod.dist_eq, Real.dist_eq] using this

lemma ee_bd (G : ℝ → ℝ → ℝ) (m M : ℝ) (K : NNReal)
    (hG : LipschitzOnWith K (fun z : ℝ × ℝ => G z.1 z.2) (Icc m M ×ˢ Icc (0 : ℝ) 1))
    {a u : ℝ} (ha : a ∈ Icc m M) (hu : u ∈ Icc (0:ℝ) 1) :
    |G a u| ≤ |G m 0| + K * ((M - m) + 1) := by
  have hm : m ∈ Icc m M := ⟨le_rfl, ha.1.trans ha.2⟩
  have := hG.dist_le_mul (x := (a,u)) (y := (m,0)) ⟨ha, hu⟩ ⟨hm, ⟨le_rfl, zero_le_one⟩⟩
  simp only [Prod.dist_eq, Real.dist_eq] at this
  have h1 : |a - m| ≤ (M-m)+1 := by
    rw [abs_of_nonneg (by linarith [ha.1])]; linarith [ha.2]
  have h2 : |u - 0| ≤ (M-m)+1 := by
    rw [sub_zero, abs_of_nonneg hu.1]; linarith [hu.2, ha.1, ha.2]
  have h3 : (K:ℝ) * max |a-m| |u-0| ≤ K * ((M-m)+1) :=
    mul_le_mul_of_nonneg_left (max_le h1 h2) K.2
  have h4 : |G a u| ≤ |G a u - G m 0| + |G m 0| := by
    have := abs_add_le (G a u - G m 0) (G m 0)
    simpa using this
  linarith

theorem euler_core (G : ℝ → ℝ → ℝ) (m M T : ℝ) (K : NNReal) (hT : 0 ≤ T)
    (hG : LipschitzOnWith K (fun z : ℝ × ℝ => G z.1 z.2) (Icc m M ×ˢ Icc (0 : ℝ) 1)) :
    ∃ κ : ℝ, ∀ n : ℕ, 0 < n → ∀ (c : ℝ) (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      (∀ k ≤ horizonSteps T n, eulerTraj G c n φs k ∈ Icc m M) →
      IsTrajectory G c (stepControl n φs) T x →
      (∀ t ∈ Icc 0 T, x t ∈ Icc m M) →
      ∀ t ∈ Icc 0 T, |x t - eulerTraj G c n φs ⌊t * n⌋₊| ≤ κ / n := by
  refine ⟨(|G m 0| + K * ((M - m) + 1)) + K * (|G m 0| + K * ((M - m) + 1)) * T * Real.exp (K * T), ?_⟩
  intro n hn c φs x hφ hE hx hxin t ht
  generalize hB0 : |G m 0| + K * ((M - m) + 1) = B0
  have hm_le : m ≤ M := (hxin 0 ⟨le_rfl, hT⟩).1.trans (hxin 0 ⟨le_rfl, hT⟩).2
  have hB0nn : 0 ≤ B0 := by
    rw [← hB0]
    have : 0 ≤ M - m := by linarith
    positivity
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hK : (0:ℝ) ≤ K := K.2
  obtain ⟨_, hxint, hxeq⟩ := hx
  set g : ℝ → ℝ := fun s => G (x s) (stepControl n φs s) with hg
  have hidx : ∀ s ∈ Icc 0 T, ⌊s * n⌋₊ ≤ horizonSteps T n := fun s hs =>
    Nat.floor_mono (mul_le_mul_of_nonneg_right hs.2 hnpos.le)
  have hgbd : ∀ s ∈ Icc 0 T, |g s| ≤ B0 := fun s hs => by
    rw [← hB0]; exact ee_bd G m M K hG (hxin s hs) (hφ _ (hidx s hs))
  have hII : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → IntervalIntegrable g volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hxint.mono_set (Icc_subset_Icc ha hb)
  have hdiff : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → x b - x a = ∫ s in a..b, g s := by
    intro a b ha hab hb
    rw [hxeq b ⟨ha.trans hab, hb⟩, hxeq a ⟨ha, hab.trans hb⟩]
    rw [← intervalIntegral.integral_interval_sub_left (hII 0 b le_rfl (ha.trans hab) hb)
      (hII 0 a le_rfl ha (hab.trans hb))]
    ring
  have hlip : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → |x b - x a| ≤ B0 * (b - a) := by
    intro a b ha hab hb
    rw [hdiff a b ha hab hb]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := g)
      (C := B0) (by
        intro s hs
        rw [uIoc_of_le hab] at hs
        rw [Real.norm_eq_abs]
        exact hgbd s ⟨ha.trans hs.1.le, hs.2.trans hb⟩)
    rwa [abs_of_nonneg (sub_nonneg.mpr hab), Real.norm_eq_abs] at this
  have hstep : ∀ k : ℕ, ((k:ℝ)+1)/n ≤ T →
      |x (((k:ℝ)+1)/n) - eulerTraj G c n φs (k+1)| ≤
        (1 + K/n) * |x (k/n) - eulerTraj G c n φs k| + K*B0/n^2 := by
    intro k hk
    have hk0 : (0:ℝ) ≤ k/n := by positivity
    have hkk : (k:ℝ)/n ≤ ((k:ℝ)+1)/n := by gcongr; linarith
    have hkT : (k:ℝ)/n ≤ T := hkk.trans hk
    have hkN : k ≤ horizonSteps T n := by
      unfold horizonSteps; apply Nat.le_floor; rw [div_le_iff₀ hnpos] at hkT; linarith
    have hxk : eulerTraj G c n φs k ∈ Icc m M := hE k hkN
    have hφk := hφ k hkN
    have hE1 : eulerTraj G c n φs (k+1) =
        eulerTraj G c n φs k + G (eulerTraj G c n φs k) (φs k) / n := rfl
    rw [hE1]
    generalize eulerTraj G c n φs k = xk at hxk ⊢
    have hint : x (((k:ℝ)+1)/n) - x (k/n) - G xk (φs k) / n =
        ∫ s in (k:ℝ)/n..((k:ℝ)+1)/n, (g s - G xk (φs k)) := by
      rw [intervalIntegral.integral_sub (hII _ _ hk0 hkk hk) intervalIntegrable_const,
        intervalIntegral.integral_const, ← hdiff _ _ hk0 hkk hk]
      simp only [smul_eq_mul]
      field_simp
      ring
    have hbound : |∫ s in (k:ℝ)/n..((k:ℝ)+1)/n, (g s - G xk (φs k))| ≤
        (K * (B0/n + |x (k/n) - xk|)) * |((k:ℝ)+1)/n - k/n| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := (k:ℝ)/n)
        (b := ((k:ℝ)+1)/n) (C := K * (B0/n + |x (k/n) - xk|))
        (f := fun s => g s - G xk (φs k)) ?_
      · simpa [Real.norm_eq_abs] using this
      have hnull : volume ({((k:ℝ)+1)/n} : Set ℝ) = 0 := measure_singleton _
      rw [ae_iff]
      refine measure_mono_null ?_ hnull
      intro s hs
      obtain ⟨hs1, hs2⟩ := Classical.not_imp.mp hs
      rw [uIoc_of_le hkk] at hs1
      rw [mem_singleton_iff]
      by_contra hne
      apply hs2
      have hslt : s < ((k:ℝ)+1)/n := lt_of_le_of_ne hs1.2 hne
      have hfl : ⌊s * n⌋₊ = k := by
        rw [Nat.floor_eq_iff (by have : 0 ≤ s := hk0.trans hs1.1.le; positivity)]
        constructor
        · have := hs1.1.le; rw [div_le_iff₀ hnpos] at this; linarith
        · rw [lt_div_iff₀ hnpos] at hslt; linarith
      have hsT : s ∈ Icc 0 T := ⟨hk0.trans hs1.1.le, hs1.2.trans hk⟩
      have hgs : g s = G (x s) (φs k) := by simp [hg, stepControl, hfl]
      rw [Real.norm_eq_abs, hgs]
      have h1 := ee_lip G m M K hG (hxin s hsT) hxk hφk
      have h2 : |x s - xk| ≤ B0/n + |x (k/n) - xk| := by
        have := hlip (k/n) s hk0 hs1.1.le hsT.2
        have h3 : B0 * (s - k/n) ≤ B0 / n := by
          rw [div_eq_mul_one_div B0]; apply mul_le_mul_of_nonneg_left _ hB0nn
          calc s - k/n ≤ ((k:ℝ)+1)/n - k/n := by linarith [hs1.2]
            _ = 1/n := by ring
        have h5 : |x s - xk| ≤ |x s - x (k/n)| + |x (k/n) - xk| := abs_sub_le _ _ _
        linarith
      calc |G (x s) (φs k) - G xk (φs k)| ≤ K * |x s - xk| := h1
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hK
    have hlen : |((k:ℝ)+1)/n - k/n| = 1/n := by
      rw [show ((k:ℝ)+1)/n - k/n = 1/n by ring]; exact abs_of_pos (by positivity)
    rw [hlen] at hbound
    have heq : x (((k:ℝ)+1)/n) - (xk + G xk (φs k) / n) =
        (x (k/n) - xk) + (x (((k:ℝ)+1)/n) - x (k/n) - G xk (φs k) / n) := by ring
    rw [heq, hint]
    have h6 := abs_add_le (x (k/n) - xk) (∫ s in (k:ℝ)/n..((k:ℝ)+1)/n, (g s - G xk (φs k)))
    have h7 : (K:ℝ) * (B0 / n + |x (k/n) - xk|) * (1/n) = (K/n) * |x (k/n) - xk| + K*B0/n^2 := by
      field_simp; ring
    nlinarith
  have hx0 : x 0 = c := by rw [hxeq 0 ⟨le_rfl, hT⟩]; simp
  have hind : ∀ k : ℕ, (k:ℝ)/n ≤ T →
      |x (k/n) - eulerTraj G c n φs k| ≤ K*B0*k/n^2*(1+K/n)^k := by
    intro k
    induction k with
    | zero => intro _; simp [eulerTraj, hx0]
    | succ k ih =>
      intro hk
      push_cast at hk ⊢
      have hk' : (k:ℝ)/n ≤ T := le_trans (by gcongr; linarith) hk
      have h0 := hstep k hk
      have ih' := ih hk'
      have hKn : 0 ≤ (K:ℝ)/n := by positivity
      have h1 : (1:ℝ) ≤ (1+K/n)^(k+1) := one_le_pow₀ (by linarith)
      have h2 : (1 + K/n) * |x (k/n) - eulerTraj G c n φs k| ≤ (1 + K/n) * (K*B0*k/n^2*(1+K/n)^k) :=
        mul_le_mul_of_nonneg_left ih' (by linarith)
      have h3 : K*B0/n^2 ≤ K*B0/n^2*(1+K/n)^(k+1) := le_mul_of_one_le_right (by positivity) h1
      calc _ ≤ (1 + K/n) * |x (k/n) - eulerTraj G c n φs k| + K*B0/n^2 := h0
        _ ≤ (1 + K/n) * (K*B0*k/n^2*(1+K/n)^k) + K*B0/n^2*(1+K/n)^(k+1) := by linarith
        _ = _ := by ring
  have ht0 : 0 ≤ t := ht.1
  have hk0 : (0:ℝ) ≤ (⌊t * n⌋₊ : ℝ)/n := by positivity
  have hkt : (⌊t * n⌋₊ : ℝ)/n ≤ t := by
    rw [div_le_iff₀ hnpos]; exact Nat.floor_le (by positivity)
  have htk : t < ((⌊t * n⌋₊ : ℝ)+1)/n := by
    rw [lt_div_iff₀ hnpos]; exact Nat.lt_floor_add_one _
  generalize ⌊t * n⌋₊ = k at hk0 hkt htk ⊢
  have hkT : (k:ℝ)/n ≤ T := hkt.trans ht.2
  have h1 := hlip (k/n) t hk0 hkt ht.2
  have h2 := hind k hkT
  have hpow : (1 + (K:ℝ)/n)^k ≤ Real.exp (K*T) := by
    calc (1 + (K:ℝ)/n)^k ≤ (Real.exp (K/n))^k := by
          have : (0:ℝ) ≤ K/n := by positivity
          gcongr
          all_goals linarith [Real.add_one_le_exp ((K:ℝ)/n)]
      _ = Real.exp (K * (k/n)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (K*T) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkT hK)
  have h3 : K*B0*k/n^2*(1+K/n)^k ≤ K*B0*T*Real.exp (K*T)/n := by
    have : K*B0*k/n^2*(1+K/n)^k = (K*B0)*(k/n)*(1+K/n)^k / n := by field_simp
    rw [this]; gcongr
  have h4 : B0 * (t - k/n) ≤ B0 / n := by
    rw [div_eq_mul_one_div B0]; apply mul_le_mul_of_nonneg_left _ hB0nn
    calc t - k/n ≤ ((k:ℝ)+1)/n - k/n := by linarith
      _ = 1/n := by ring
  have h5 := abs_sub_le (x t) (x (k/n)) (eulerTraj G c n φs k)
  have h6 : B0/n + K*B0*T*Real.exp (K*T)/n = (B0 + K*B0*T*Real.exp (K*T))/n := by ring
  linarith

end BellmanDP.Variational

open BellmanDP.Variational
open Set

theorem solution (G : ℝ → ℝ → ℝ) (m M T : ℝ) (K : NNReal) (hT : 0 ≤ T)
    (hG : LipschitzOnWith K (fun z : ℝ × ℝ => G z.1 z.2) (Icc m M ×ˢ Icc (0 : ℝ) 1)) :
    ∃ κ : ℝ, ∀ n : ℕ, 0 < n → ∀ (c : ℝ) (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      (∀ k ≤ horizonSteps T n, eulerTraj G c n φs k ∈ Icc m M) →
      IsTrajectory G c (stepControl n φs) T x →
      (∀ t ∈ Icc 0 T, x t ∈ Icc m M) →
      ∀ t ∈ Icc 0 T, |x t - eulerTraj G c n φs ⌊t * n⌋₊| ≤ κ / n := by
  exact euler_core G m M T K hT hG
