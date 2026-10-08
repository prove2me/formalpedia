-- Prove2me | solution 1 for BellmanDP.Variational.payoff_discretization_error
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:21:03.897338+00:00
-- url     : https://prove2.me/submissions/d91e11ca-ced2-4f60-bf93-05943564e4f9

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

open Topology Filter in
lemma pd_rderiv (G : ℝ → ℝ → ℝ) (hGc : Continuous (fun z : ℝ × ℝ => G z.1 z.2))
    (c T : ℝ) (n : ℕ) (hn : 0 < n) (φs : ℕ → ℝ) (x : ℝ → ℝ)
    (hx : IsTrajectory G c (stepControl n φs) T x) (t : ℝ) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt x (G (x t) (stepControl n φs t)) (Ici t) t := by
  obtain ⟨hxc, hxint, hxeq⟩ := hx
  set g : ℝ → ℝ := fun s => G (x s) (stepControl n φs s) with hg
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 ≤ t := ht.1
  set k := ⌊t * n⌋₊ with hk
  set b := min T (((k:ℝ)+1)/n) with hb
  have htb : t < b := lt_min ht.2 (by rw [lt_div_iff₀ hnpos]; exact Nat.lt_floor_add_one _)
  have hstep : ∀ s ∈ Ico t b, stepControl n φs s = φs k := by
    intro s hs
    simp only [stepControl]
    congr 1
    have hs0 : 0 ≤ s := ht0.trans hs.1
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · calc (k:ℝ) ≤ t * n := Nat.floor_le (by positivity)
        _ ≤ s * n := by nlinarith [hs.1]
    · have := hs.2.trans_le (min_le_right _ _); rw [lt_div_iff₀ hnpos] at this; exact this
  have hbT : b ≤ T := min_le_left _ _
  have hmem : Icc t b ∈ 𝓝[≥] t := Icc_mem_nhdsGE htb
  have hII : IntervalIntegrable g volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]
    exact hxint.mono_set (Icc_subset_Icc le_rfl ht.2.le)
  have hcont : ContinuousWithinAt g (Ioi t) t := by
    have hxw : ContinuousWithinAt x (Ico t b) t :=
      (hxc t ⟨ht0, ht.2.le⟩).mono (fun s hs => ⟨ht0.trans hs.1, hs.2.le.trans hbT⟩)
    have h1 : ContinuousWithinAt (fun s => G (x s) (φs k)) (Ico t b) t :=
      hGc.continuousAt.comp_continuousWithinAt (hxw.prodMk continuousWithinAt_const)
    have h2 : ContinuousWithinAt g (Ico t b) t :=
      h1.congr (fun y hy => by simp only [hg, hstep y hy]) (by simp only [hg, hstep t ⟨le_rfl, htb⟩])
    exact h2.mono_of_mem_nhdsWithin (mem_of_superset (Ioo_mem_nhdsGT htb) Ioo_subset_Ico_self)
  have hmeas : StronglyMeasurableAtFilter g (𝓝[>] t) :=
    ⟨Ioo t b, Ioo_mem_nhdsGT htb, (hxint.mono_set (fun s hs =>
      ⟨ht0.trans hs.1.le, hs.2.le.trans hbT⟩)).aestronglyMeasurable⟩
  have hd : HasDerivWithinAt (fun u => ∫ s in (0:ℝ)..u, g s) (g t) (Ici t) t :=
    intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t) hII hmeas hcont
  have hd2 : HasDerivWithinAt x (g t) (Icc t b) t := by
    have := (hd.const_add c).mono (Icc_subset_Ici_self : Icc t b ⊆ Ici t)
    refine this.congr (fun y hy => hxeq y ⟨ht0.trans hy.1, hy.2.trans hbT⟩)
      (hxeq t ⟨ht0, ht.2.le⟩)
  exact hd2.mono_of_mem_nhdsWithin hmem

lemma pd_expderiv (C a t : ℝ) :
    HasDerivWithinAt (fun s => C * Real.exp (a * s)) (a * (C * Real.exp (a * t))) (Ici t) t := by
  have := (((hasDerivAt_id t).const_mul a).exp.const_mul C)
  exact (this.congr_deriv (by simp; ring)).hasDerivWithinAt

lemma pd_traj_bounds (G : ℝ → ℝ → ℝ) (hGc : Continuous (fun z : ℝ × ℝ => G z.1 z.2))
    (p q r : ℝ) (hpqr : ∀ x y : ℝ, 0 < x → 0 ≤ y → y ≤ x → p * x ≤ G x y ∧ G x y ≤ q * x + r)
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (n : ℕ) (hn : 0 < n) (φs : ℕ → ℝ) (x : ℝ → ℝ)
    (hφ : ∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1)
    (hx : IsTrajectory (phiForm G) c (stepControl n φs) T x) :
    ∀ t ∈ Icc 0 T, (c/2) * Real.exp (-(|p|+1) * t) ≤ x t ∧
      x t ≤ (c + |r| + 1) * Real.exp ((|q|+1) * t) := by
  have hGc' : Continuous (fun z : ℝ × ℝ => phiForm G z.1 z.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_snd.mul continuous_fst))
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hder := pd_rderiv (phiForm G) hGc' c T n hn φs x hx
  have hxc := hx.1
  have hx0 : x 0 = c := by rw [hx.2.2 0 ⟨le_rfl, hT.le⟩]; simp
  have hφt : ∀ t ∈ Ico 0 T, stepControl n φs t ∈ Icc (0:ℝ) 1 := fun t ht =>
    hφ _ (Nat.floor_mono (mul_le_mul_of_nonneg_right ht.2.le hnpos.le))
  have hGx : ∀ t ∈ Ico 0 T, 0 < x t →
      p * x t ≤ phiForm G (x t) (stepControl n φs t) ∧
        phiForm G (x t) (stepControl n φs t) ≤ q * x t + r := by
    intro t ht hxt
    have h := hφt t ht
    exact hpqr (x t) _ hxt (mul_nonneg h.1 hxt.le) (by nlinarith [h.2])
  intro t ht
  constructor
  · have hbd : ∀ s ∈ Ico (0:ℝ) T, (fun s => - x s) s = (fun s => -(c/2) * Real.exp (-(|p|+1) * s)) s →
        (fun s => - phiForm G (x s) (stepControl n φs s)) s <
          (fun s => (-(|p|+1)) * (-(c/2) * Real.exp (-(|p|+1) * s))) s := by
      intro s hs heq
      beta_reduce at heq ⊢
      have hxs : x s = (c/2) * Real.exp (-(|p|+1) * s) := by linarith
      have hpos : 0 < x s := by rw [hxs]; positivity
      have := (hGx s hs hpos).1
      have hp : -|p| ≤ p := neg_abs_le p
      have h1 := mul_le_mul_of_nonneg_right hp hpos.le
      have h2 : -(|p|+1) * (-(c/2) * Real.exp (-(|p|+1) * s)) = |p| * x s + x s := by rw [hxs]; ring
      rw [h2]; linarith
    have hBc : ContinuousOn (fun s => -(c/2) * Real.exp (-(|p|+1) * s)) (Icc 0 T) := by fun_prop
    have key : -x t ≤ -(c/2) * Real.exp (-(|p|+1) * t) :=
      image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T)
        (f := fun s => - x s) (f' := fun s => - phiForm G (x s) (stepControl n φs s))
        (B := fun s => -(c/2) * Real.exp (-(|p|+1) * s))
        (B' := fun s => (-(|p|+1)) * (-(c/2) * Real.exp (-(|p|+1) * s)))
        hxc.neg (fun s hs => (hder s hs).neg)
        (by show -x 0 ≤ -(c/2) * Real.exp (-(|p|+1) * 0); rw [hx0, mul_zero, Real.exp_zero, mul_one]; linarith)
        hBc (fun s _ => pd_expderiv _ _ s) hbd ht
    linarith
  · have hbd : ∀ s ∈ Ico (0:ℝ) T, x s = (fun s => (c + |r| + 1) * Real.exp ((|q|+1) * s)) s →
        (fun s => phiForm G (x s) (stepControl n φs s)) s <
          (fun s => (|q|+1) * ((c + |r| + 1) * Real.exp ((|q|+1) * s))) s := by
      intro s hs heq
      beta_reduce at heq ⊢
      have he : 1 ≤ Real.exp ((|q|+1) * s) := Real.one_le_exp (by nlinarith [hs.1, abs_nonneg q])
      have hBr : |r| < (c + |r| + 1) * Real.exp ((|q|+1) * s) := by nlinarith [abs_nonneg r]
      have hpos : 0 < x s := by rw [heq]; linarith [abs_nonneg r]
      have := (hGx s hs hpos).2
      have hq : q ≤ |q| := le_abs_self q
      have hr : r ≤ |r| := le_abs_self r
      rw [heq] at this ⊢
      have h1 := mul_le_mul_of_nonneg_right hq (by linarith : (0:ℝ) ≤ (c + |r| + 1) * Real.exp ((|q|+1) * s))
      linarith
    have hBc : ContinuousOn (fun s => (c + |r| + 1) * Real.exp ((|q|+1) * s)) (Icc 0 T) := by fun_prop
    exact image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T)
      (f := x) (f' := fun s => phiForm G (x s) (stepControl n φs s))
      (B := fun s => (c + |r| + 1) * Real.exp ((|q|+1) * s))
      (B' := fun s => (|q|+1) * ((c + |r| + 1) * Real.exp ((|q|+1) * s)))
      hxc hder
      (by show x 0 ≤ (c + |r| + 1) * Real.exp ((|q|+1) * 0); rw [hx0, mul_zero, Real.exp_zero, mul_one]; linarith [abs_nonneg r])
      hBc (fun s _ => pd_expderiv _ _ s) hbd ht
lemma pd_euler_bounds (G : ℝ → ℝ → ℝ)
    (p q r : ℝ) (hpqr : ∀ x y : ℝ, 0 < x → 0 ≤ y → y ≤ x → p * x ≤ G x y ∧ G x y ≤ q * x + r)
    (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 0 < n) (hpn : 2 * |p| ≤ n)
    (φs : ℕ → ℝ) (N : ℕ) (hφ : ∀ k ≤ N, φs k ∈ Icc (0 : ℝ) 1) :
    ∀ k ≤ N, c * Real.exp (-(2*|p|) * (k/n)) ≤ eulerTraj (phiForm G) c n φs k ∧
      eulerTraj (phiForm G) c n φs k ≤ (c + |r| + 1) * Real.exp ((|q|+1) * (k/n)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  intro k
  induction k with
  | zero => intro _; simp [eulerTraj]; linarith [abs_nonneg r]
  | succ k ih =>
    intro hk
    obtain ⟨ihl, ihu⟩ := ih (by omega)
    have hφk := hφ k (by omega)
    have hE : eulerTraj (phiForm G) c n φs (k+1) =
        eulerTraj (phiForm G) c n φs k + G (eulerTraj (phiForm G) c n φs k)
          (φs k * eulerTraj (phiForm G) c n φs k) / n := rfl
    rw [hE]
    generalize eulerTraj (phiForm G) c n φs k = xk at ihl ihu ⊢
    have hpos : 0 < xk := lt_of_lt_of_le (by positivity) ihl
    obtain ⟨hl, hu⟩ := hpqr xk (φs k * xk) hpos (mul_nonneg hφk.1 hpos.le) (by nlinarith [hφk.2])
    push_cast
    constructor
    · have hu0 : 0 ≤ |p| / n := by positivity
      have hu1 : |p| / n ≤ 1/2 := by
        rw [div_le_iff₀ hnpos]; linarith
      have hexp : Real.exp (-(2*|p|) * ((k+1)/n)) =
          Real.exp (-(2*|p|) * (k/n)) * Real.exp (-2*(|p|/n)) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring
      have hkey : Real.exp (-2*(|p|/n)) ≤ 1 - |p|/n := by
        have h1 := Real.add_one_le_exp (2*(|p|/n))
        have h2 : Real.exp (-2*(|p|/n)) * Real.exp (2*(|p|/n)) = 1 := by
          rw [← Real.exp_add]; simp
        have h3 : 0 < Real.exp (-2*(|p|/n)) := Real.exp_pos _
        nlinarith
      have hGl : -|p| * xk / n ≤ G xk (φs k * xk) / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le
        nlinarith [neg_abs_le p]
      have h4 : xk + -|p| * xk / n = xk * (1 - |p|/n) := by ring
      rw [hexp]
      have h5 : c * Real.exp (-(2*|p|) * (k/n)) * Real.exp (-2*(|p|/n)) ≤ xk * (1 - |p|/n) :=
        mul_le_mul ihl hkey (Real.exp_pos _).le hpos.le
      have h6 : c * (Real.exp (-(2*|p|) * (k/n)) * Real.exp (-2*(|p|/n))) =
          c * Real.exp (-(2*|p|) * (k/n)) * Real.exp (-2*(|p|/n)) := by ring
      linarith
    · have hexp : Real.exp ((|q|+1) * ((k+1)/n)) =
          Real.exp ((|q|+1) * (k/n)) * Real.exp ((|q|+1)/n) := by
        rw [← Real.exp_add]; congr 1; field_simp
      have hE1 : 1 ≤ Real.exp ((|q|+1) * (k/n)) := Real.one_le_exp (by positivity)
      have hkey : 1 + (|q|+1)/n ≤ Real.exp ((|q|+1)/n) := by
        linarith [Real.add_one_le_exp ((|q|+1)/n)]
      rw [hexp]
      generalize Real.exp ((|q|+1) * (k/n)) = E at hE1 ihu ⊢
      have hDpos : 0 < c + |r| + 1 := by positivity
      have hD : |r| ≤ (c + |r| + 1) * E := by nlinarith [abs_nonneg r]
      have hGu : G xk (φs k * xk) ≤ |q| * xk + |r| := by
        nlinarith [le_abs_self q, le_abs_self r]
      have h3 : G xk (φs k * xk) / n ≤ (|q| * ((c + |r| + 1) * E) + (c + |r| + 1) * E) / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le; nlinarith [abs_nonneg q]
      have h2 : (c + |r| + 1) * E * (1 + (|q|+1)/n) =
          (c + |r| + 1) * E + (|q| * ((c + |r| + 1) * E) + (c + |r| + 1) * E) / n := by
        field_simp
      have h4 : (c + |r| + 1) * E * (1 + (|q|+1)/n) ≤ (c + |r| + 1) * E * Real.exp ((|q|+1)/n) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      have h5 : (c + |r| + 1) * (E * Real.exp ((|q|+1)/n)) =
          (c + |r| + 1) * E * Real.exp ((|q|+1)/n) := by ring
      linarith

lemma pd_crude (F G : ℝ → ℝ → ℝ) (hFc : Continuous (fun z : ℝ × ℝ => F z.1 z.2))
    (hGc : Continuous (fun z : ℝ × ℝ => G z.1 z.2)) (c : ℝ) (n N : ℕ) :
    ∃ D : ℝ, ∀ φs : ℕ → ℝ, (∀ k ≤ N, φs k ∈ Icc (0:ℝ) 1) →
      |discretePayoff F G c n φs N| ≤ D := by
  have hR : ∀ k : ℕ, ∃ R : ℝ, ∀ φs : ℕ → ℝ, (∀ j < k, φs j ∈ Icc (0:ℝ) 1) →
      |eulerTraj G c n φs k| ≤ R := by
    intro k
    induction k with
    | zero => exact ⟨|c|, fun φs _ => by simp [eulerTraj]⟩
    | succ k ih =>
      obtain ⟨R, hR⟩ := ih
      obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Icc (-R) R ×ˢ Icc (0:ℝ) 1)).exists_bound_of_continuousOn hGc.continuousOn
      refine ⟨R + |C / n|, fun φs hφ => ?_⟩
      have h1 := hR φs (fun j hj => hφ j (by omega))
      have h2 := hC (eulerTraj G c n φs k, φs k) ⟨abs_le.mp h1, hφ k (by omega)⟩
      rw [Real.norm_eq_abs] at h2
      show |eulerTraj G c n φs k + G (eulerTraj G c n φs k) (φs k) / n| ≤ _
      have h3 : |G (eulerTraj G c n φs k) (φs k) / n| ≤ |C / n| := by
        rw [abs_div, abs_div]; exact div_le_div_of_nonneg_right (h2.trans (le_abs_self _)) (abs_nonneg _)
      linarith [abs_add_le (eulerTraj G c n φs k) (G (eulerTraj G c n φs k) (φs k) / n)]
  choose R hR using hR
  have hC : ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ Icc (-R k) (R k) ×ˢ Icc (0:ℝ) 1, ‖F z.1 z.2‖ ≤ C :=
    fun k => (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hFc.continuousOn
  choose C hC using hC
  refine ⟨∑ k ∈ Finset.range (N+1), |C k / n|, fun φs hφ => ?_⟩
  unfold discretePayoff
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 := hR k φs (fun j hj => hφ j (by omega))
  have h2 := hC k (eulerTraj G c n φs k, φs k) ⟨abs_le.mp h1, hφ k hk⟩
  rw [Real.norm_eq_abs] at h2
  rw [abs_div, abs_div]; exact div_le_div_of_nonneg_right (h2.trans (le_abs_self _)) (abs_nonneg _)

lemma pd_step_int (f : ℝ → ℝ) (a b v : ℝ) (hab : a ≤ b) (hf : ∀ s ∈ Ico a b, f s = v) :
    ∫ s in a..b, f s = (b - a) * v := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (fun s hs => hf s ⟨hs.1.le, hs.2⟩)]
  simp [hab]

lemma pd_floor (n : ℕ) (hn : (0:ℝ) < n) (k : ℕ) (s : ℝ)
    (hs : s ∈ Ico ((k:ℝ)/n) (((k:ℝ)+1)/n)) : ⌊s * n⌋₊ = k := by
  have h0 : 0 ≤ s := le_trans (by positivity) hs.1
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · have := hs.1; rw [div_le_iff₀ hn] at this; linarith
  · have := hs.2; rw [lt_div_iff₀ hn] at this; linarith
theorem pd_core (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n → ∀ (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      IsTrajectory (phiForm G) c (stepControl n φs) T x →
      |(∫ t in (0 : ℝ)..T, phiForm F (x t) (stepControl n φs t)) -
          discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n)| ≤ B / n := by
  obtain ⟨hF2, hG2, ⟨p, q, r, hpqr⟩, -⟩ := hFG
  have hsub : ContDiff ℝ 2 (fun z : ℝ × ℝ => (z.1, z.2 * z.1)) :=
    contDiff_fst.prodMk (contDiff_snd.mul contDiff_fst)
  have hF' : ContDiff ℝ 2 (fun z : ℝ × ℝ => phiForm F z.1 z.2) := hF2.comp hsub
  have hG' : ContDiff ℝ 2 (fun z : ℝ × ℝ => phiForm G z.1 z.2) := hG2.comp hsub
  have hGc : Continuous (fun z : ℝ × ℝ => G z.1 z.2) := hG2.continuous
  have hFc' := hF'.continuous
  have hGc' := hG'.continuous
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = (c/2) * Real.exp (-(2*(|p|+1)) * T) := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi, hi = (c + |r| + 1) * Real.exp ((|q|+1) * T) := ⟨_, rfl⟩
  have hboxc : IsCompact (Icc lo hi ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hboxv : Convex ℝ (Icc lo hi ×ˢ Icc (0:ℝ) 1) := (convex_Icc _ _).prod (convex_Icc _ _)
  obtain ⟨KG, hKG⟩ := hG'.contDiffOn.exists_lipschitzOnWith (by norm_num) hboxv hboxc
  obtain ⟨KF, hKF⟩ := hF'.contDiffOn.exists_lipschitzOnWith (by norm_num) hboxv hboxc
  obtain ⟨BF, hBF⟩ := hboxc.exists_bound_of_continuousOn hFc'.continuousOn
  obtain ⟨κ, hκ⟩ := euler_core (phiForm G) lo hi T KG hT.le hKG
  have hcr : ∀ n : ℕ, ∃ D : ℝ, ∀ φs : ℕ → ℝ, (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0:ℝ) 1) →
      |discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n)| ≤ D :=
    fun n => pd_crude _ _ hFc' hGc' c n _
  choose D hD using hcr
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, n0 = ⌈2*|p|⌉₊ + 1 := ⟨_, rfl⟩
  have hBFn : 0 ≤ |BF| := abs_nonneg _
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range n0, (j:ℝ) * (T * |BF| + |D j|) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  refine ⟨∑ j ∈ Finset.range n0, (j:ℝ) * (T * |BF| + |D j|) + (T * KF * |κ| + |BF|), ?_⟩
  intro n hn φs x hφ hx
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hxb : ∀ t ∈ Icc 0 T, x t ∈ Icc lo hi := by
    intro t ht
    obtain ⟨h1, h2⟩ := pd_traj_bounds G hGc p q r hpqr c T hc hT n hn φs x hφ hx t ht
    constructor
    · refine le_trans ?_ h1
      rw [hlo]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [ht.1, ht.2, abs_nonneg p]
    · refine h2.trans ?_
      rw [hhi]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [ht.1, ht.2, abs_nonneg q]
  have hφt : ∀ t ∈ Icc 0 T, stepControl n φs t ∈ Icc (0:ℝ) 1 := fun t ht =>
    hφ _ (Nat.floor_mono (mul_le_mul_of_nonneg_right ht.2 hnpos.le))
  have hmeasφ : Measurable (stepControl n φs) := by
    unfold stepControl
    exact measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_id.mul_const _))
  have hfbd : ∀ t ∈ Icc 0 T, |phiForm F (x t) (stepControl n φs t)| ≤ BF := fun t ht => by
    have := hBF (x t, stepControl n φs t) ⟨hxb t ht, hφt t ht⟩
    rwa [Real.norm_eq_abs] at this
  have hI1 : IntervalIntegrable (fun t => phiForm F (x t) (stepControl n φs t)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
    have hxm : AEMeasurable x (volume.restrict (Icc 0 T)) :=
      (hx.1.aestronglyMeasurable measurableSet_Icc).aemeasurable
    refine ⟨(hFc'.measurable.comp_aemeasurable (hxm.prodMk hmeasφ.aemeasurable)).aestronglyMeasurable,
      HasFiniteIntegral.restrict_of_bounded (C := BF) (by simp) ?_⟩
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
    rw [Real.norm_eq_abs]; exact hfbd t ht
  have hT0 : |T - 0| = T := by rw [sub_zero, abs_of_pos hT]
  by_cases hlarge : n0 ≤ n
  · -- large n
    set N := horizonSteps T n with hN
    have hpn : 2 * |p| ≤ n := by
      have h1 : 2 * |p| ≤ (⌈2*|p|⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈2*|p|⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈2*|p|⌉₊ ≤ n)
      linarith
    have hNT : (N:ℝ) ≤ T * n := Nat.floor_le (by positivity)
    have hNT' : T * n < (N:ℝ) + 1 := Nat.lt_floor_add_one _
    have hEb : ∀ k ≤ N, eulerTraj (phiForm G) c n φs k ∈ Icc lo hi := by
      intro k hk
      obtain ⟨h1, h2⟩ := pd_euler_bounds G p q r hpqr c hc n hn hpn φs N hφ k hk
      have hkT : (k:ℝ)/n ≤ T := by
        rw [div_le_iff₀ hnpos]
        have : (k:ℝ) ≤ N := by exact_mod_cast hk
        linarith
      have hk0 : (0:ℝ) ≤ k/n := by positivity
      constructor
      · refine le_trans ?_ h1
        rw [hlo]
        have e1 : Real.exp (-(2*(|p|+1)) * T) ≤ Real.exp (-(2*|p|) * (k/n)) := by
          apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg p]
        have e2 : 0 < Real.exp (-(2*(|p|+1)) * T) := Real.exp_pos _
        nlinarith
      · refine h2.trans ?_
        rw [hhi]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [abs_nonneg q]
    have hκb := hκ n hn c φs x hφ hEb hx hxb
    -- step function
    set h : ℝ → ℝ := fun t => phiForm F (eulerTraj (phiForm G) c n φs (min ⌊t * n⌋₊ N))
      (φs (min ⌊t * n⌋₊ N)) with hh
    have hhbd : ∀ t, |h t| ≤ BF := by
      intro t
      have hm : min ⌊t * n⌋₊ N ≤ N := min_le_right _ _
      have := hBF (eulerTraj (phiForm G) c n φs (min ⌊t * n⌋₊ N), φs (min ⌊t * n⌋₊ N))
        ⟨hEb _ hm, hφ _ hm⟩
      rwa [Real.norm_eq_abs] at this
    have hhmeas : Measurable h := by
      have : h = (fun k : ℕ => phiForm F (eulerTraj (phiForm G) c n φs (min k N)) (φs (min k N)))
          ∘ (fun t : ℝ => ⌊t * n⌋₊) := rfl
      rw [this]
      exact measurable_from_nat.comp (Nat.measurable_floor.comp (measurable_id.mul_const _))
    have hhI : ∀ a b : ℝ, IntervalIntegrable h volume a b := by
      intro a b
      rw [intervalIntegrable_iff]
      refine Measure.integrableOn_of_bounded (M := BF) ?_ hhmeas.aestronglyMeasurable ?_
      · simp [uIoc]
      · exact Filter.Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hhbd t)
    have hS : discretePayoff (phiForm F) (phiForm G) c n φs N = ∫ t in (0:ℝ)..((N:ℝ)+1)/n, h t := by
      have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := h)
        (a := fun k : ℕ => (k:ℝ)/n) (n := N+1) (fun k _ => hhI _ _)
      simp only [Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one] at hsum
      rw [← hsum]
      unfold discretePayoff
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [pd_step_int h _ _ (phiForm F (eulerTraj (phiForm G) c n φs k) (φs k))
        (by gcongr; linarith)]
      · field_simp
        ring
      · intro s hs
        have hfl := pd_floor n hnpos k s hs
        simp only [hh, hfl, min_eq_left hk]
    have hsplit : ∫ t in (0:ℝ)..((N:ℝ)+1)/n, h t =
        (∫ t in (0:ℝ)..T, h t) + ∫ t in T..((N:ℝ)+1)/n, h t :=
      (intervalIntegral.integral_add_adjacent_intervals (hhI _ _) (hhI _ _)).symm
    have hdiffI : |(∫ t in (0:ℝ)..T, phiForm F (x t) (stepControl n φs t)) - ∫ t in (0:ℝ)..T, h t|
        ≤ (KF * (κ / n)) * T := by
      rw [← intervalIntegral.integral_sub hI1 (hhI _ _)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
        (f := fun t => phiForm F (x t) (stepControl n φs t) - h t) (C := KF * (κ / n)) (by
          intro t ht
          rw [uIoc_of_le hT.le] at ht
          have htI : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
          have hm : ⌊t * n⌋₊ ≤ N := Nat.floor_mono (mul_le_mul_of_nonneg_right ht.2 hnpos.le)
          have hht : h t = phiForm F (eulerTraj (phiForm G) c n φs ⌊t * n⌋₊) (stepControl n φs t) := by
            simp only [hh, min_eq_left hm, stepControl]
          rw [Real.norm_eq_abs, hht]
          have h1 := ee_lip (phiForm F) lo hi KF hKF (hxb t htI) (hEb _ hm) (hφt t htI)
          have h2 := hκb t htI
          calc _ ≤ (KF:ℝ) * |x t - eulerTraj (phiForm G) c n φs ⌊t * n⌋₊| := h1
            _ ≤ _ := mul_le_mul_of_nonneg_left h2 KF.2)
      rwa [Real.norm_eq_abs, hT0] at this
    have htail : |∫ t in T..((N:ℝ)+1)/n, h t| ≤ |BF| / n := by
      have hle : T ≤ ((N:ℝ)+1)/n := by rw [le_div_iff₀ hnpos]; linarith
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := ((N:ℝ)+1)/n)
        (f := h) (C := |BF|) (fun t _ => by
          rw [Real.norm_eq_abs]; exact (hhbd t).trans (le_abs_self _))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] at this
      have hlen : ((N:ℝ)+1)/n - T ≤ 1/n := by
        rw [div_sub' hnpos.ne', div_le_div_iff_of_pos_right hnpos]; linarith
      calc _ ≤ |BF| * (((N:ℝ)+1)/n - T) := this
        _ ≤ |BF| * (1/n) := mul_le_mul_of_nonneg_left hlen hBFn
        _ = |BF| / n := by ring
    rw [hS, hsplit]
    have hκn : KF * (κ / n) * T ≤ T * KF * |κ| / n := by
      have : (KF:ℝ) * (κ / n) * T = T * KF * κ / n := by ring
      rw [this]
      apply div_le_div_of_nonneg_right _ hnpos.le
      apply mul_le_mul_of_nonneg_left (le_abs_self κ)
      exact mul_nonneg hT.le KF.2
    have hfin : T * KF * |κ| / n + |BF| / n ≤
        (∑ j ∈ Finset.range n0, (j:ℝ) * (T * |BF| + |D j|) + (T * KF * |κ| + |BF|)) / n := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hnpos.le
      linarith
    have h3 := abs_sub_le ((∫ t in (0:ℝ)..T, phiForm F (x t) (stepControl n φs t)))
      (∫ t in (0:ℝ)..T, h t) ((∫ t in (0:ℝ)..T, h t) + ∫ t in T..((N:ℝ)+1)/n, h t)
    have h4 : |(∫ t in (0:ℝ)..T, h t) - ((∫ t in (0:ℝ)..T, h t) + ∫ t in T..((N:ℝ)+1)/n, h t)| =
        |∫ t in T..((N:ℝ)+1)/n, h t| := by
      rw [show (∫ t in (0:ℝ)..T, h t) - ((∫ t in (0:ℝ)..T, h t) + ∫ t in T..((N:ℝ)+1)/n, h t) =
        -∫ t in T..((N:ℝ)+1)/n, h t by ring, abs_neg]
    linarith
  · -- small n
    push Not at hlarge
    have hI : |∫ t in (0 : ℝ)..T, phiForm F (x t) (stepControl n φs t)| ≤ T * |BF| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
        (f := fun t => phiForm F (x t) (stepControl n φs t)) (C := |BF|) (by
          intro t ht
          rw [uIoc_of_le hT.le] at ht
          rw [Real.norm_eq_abs]; exact (hfbd t ⟨ht.1.le, ht.2⟩).trans (le_abs_self _))
      rw [Real.norm_eq_abs, hT0] at this; linarith
    have hDn := hD n φs hφ
    have hmem : n ∈ Finset.range n0 := Finset.mem_range.mpr hlarge
    have hsingle : (n:ℝ) * (T * |BF| + |D n|) ≤ ∑ j ∈ Finset.range n0, (j:ℝ) * (T * |BF| + |D j|) :=
      Finset.single_le_sum (f := fun j : ℕ => (j:ℝ) * (T * |BF| + |D j|))
        (fun j _ => by positivity) hmem
    have hpos2 : 0 ≤ T * KF * |κ| + |BF| := by have := KF.2; positivity
    rw [le_div_iff₀ hnpos]
    have h2 : |(∫ t in (0 : ℝ)..T, phiForm F (x t) (stepControl n φs t)) -
        discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n)| ≤ T * |BF| + |D n| := by
      have := abs_sub (∫ t in (0 : ℝ)..T, phiForm F (x t) (stepControl n φs t))
        (discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n))
      linarith [le_abs_self (D n)]
    have h3 := mul_le_mul_of_nonneg_left h2 hnpos.le
    nlinarith

end BellmanDP.Variational

open BellmanDP.Variational
open Set

theorem solution (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n → ∀ (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      IsTrajectory (phiForm G) c (stepControl n φs) T x →
      |(∫ t in (0 : ℝ)..T, phiForm F (x t) (stepControl n φs t)) -
          discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n)| ≤ B / n := by
  exact pd_core F G hFG c T hc hT
