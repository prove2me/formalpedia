-- Prove2me | solution 1 for DeepONetUniversal.number_of_sensors
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T23:45:24.569137+00:00
-- url     : https://prove2.me/submissions/7788973c-0184-4ef0-bc4d-da7badf05f1e

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic

open MeasureTheory Filter Topology DeepONetUniversal
open scoped Convolution ContDiff

/-! ### Part 1: Every continuous non-polynomial function is Tauber-Wiener -/

private def InSpanClosure (σ : ℝ → ℝ) (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ (N : ℕ) (c lam θ : Fin N → ℝ),
    ∀ x ∈ Set.Icc a b, |g x - ∑ i, c i * σ (lam i * x + θ i)| < ε

private lemma inSpanClosure_zero (σ : ℝ → ℝ) (a b : ℝ) :
    InSpanClosure σ a b (fun _ => 0) := by
  intro ε hε
  exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun _ _ => by simpa using hε⟩

private lemma inSpanClosure_gen (σ : ℝ → ℝ) (a b lam θ : ℝ) :
    InSpanClosure σ a b (fun x => σ (lam * x + θ)) := by
  intro ε hε
  refine ⟨1, fun _ => 1, fun _ => lam, fun _ => θ, fun x _ => ?_⟩
  simpa using hε

private lemma inSpanClosure_smul {σ : ℝ → ℝ} {a b : ℝ} {g : ℝ → ℝ} (r : ℝ)
    (hg : InSpanClosure σ a b g) :
    InSpanClosure σ a b (fun x => r * g x) := by
  intro ε hε
  have hδ : 0 < ε / (|r| + 1) := by positivity
  obtain ⟨N, c, lam, θ, hN⟩ := hg _ hδ
  refine ⟨N, fun i => r * c i, lam, θ, fun x hx => ?_⟩
  have h1 : r * g x - ∑ i, (r * c i) * σ (lam i * x + θ i) =
      r * (g x - ∑ i, c i * σ (lam i * x + θ i)) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1, abs_mul]
  have hlt := hN x hx
  have hrpos : 0 < |r| + 1 := by positivity
  calc |r| * |g x - ∑ i, c i * σ (lam i * x + θ i)|
      ≤ |r| * (ε / (|r| + 1)) := by gcongr
    _ < (|r| + 1) * (ε / (|r| + 1)) := by nlinarith
    _ = ε := by field_simp [hrpos.ne']

private lemma inSpanClosure_add {σ : ℝ → ℝ} {a b : ℝ} {g₁ g₂ : ℝ → ℝ}
    (hg₁ : InSpanClosure σ a b g₁) (hg₂ : InSpanClosure σ a b g₂) :
    InSpanClosure σ a b (fun x => g₁ x + g₂ x) := by
  intro ε hε
  obtain ⟨N₁, c₁, lam₁, θ₁, h₁⟩ := hg₁ (ε / 2) (half_pos hε)
  obtain ⟨N₂, c₂, lam₂, θ₂, h₂⟩ := hg₂ (ε / 2) (half_pos hε)
  refine ⟨N₁ + N₂, Fin.append c₁ c₂, Fin.append lam₁ lam₂, Fin.append θ₁ θ₂, fun x hx => ?_⟩
  have hsum : (∑ i : Fin (N₁ + N₂),
      Fin.append c₁ c₂ i * σ (Fin.append lam₁ lam₂ i * x + Fin.append θ₁ θ₂ i)) =
      (∑ i : Fin N₁, c₁ i * σ (lam₁ i * x + θ₁ i)) +
      (∑ i : Fin N₂, c₂ i * σ (lam₂ i * x + θ₂ i)) := by
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  rw [hsum]
  have ha := h₁ x hx
  have hb := h₂ x hx
  have heq : g₁ x + g₂ x - ((∑ i, c₁ i * σ (lam₁ i * x + θ₁ i)) +
        (∑ i, c₂ i * σ (lam₂ i * x + θ₂ i))) =
      (g₁ x - ∑ i, c₁ i * σ (lam₁ i * x + θ₁ i)) +
        (g₂ x - ∑ i, c₂ i * σ (lam₂ i * x + θ₂ i)) := by ring
  rw [heq]
  calc |(g₁ x - ∑ i, c₁ i * σ (lam₁ i * x + θ₁ i)) +
          (g₂ x - ∑ i, c₂ i * σ (lam₂ i * x + θ₂ i))|
      ≤ |g₁ x - ∑ i, c₁ i * σ (lam₁ i * x + θ₁ i)| +
          |g₂ x - ∑ i, c₂ i * σ (lam₂ i * x + θ₂ i)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add ha hb
    _ = ε := add_halves ε

private lemma inSpanClosure_sub {σ : ℝ → ℝ} {a b : ℝ} {g₁ g₂ : ℝ → ℝ}
    (hg₁ : InSpanClosure σ a b g₁) (hg₂ : InSpanClosure σ a b g₂) :
    InSpanClosure σ a b (fun x => g₁ x - g₂ x) := by
  have := inSpanClosure_add hg₁ (inSpanClosure_smul (-1) hg₂)
  simpa [sub_eq_add_neg] using this

private lemma inSpanClosure_of_uniform_approx {σ : ℝ → ℝ} {a b : ℝ} {h : ℝ → ℝ}
    (hh : ∀ ε > 0, ∃ g, InSpanClosure σ a b g ∧ ∀ x ∈ Set.Icc a b, |h x - g x| < ε) :
    InSpanClosure σ a b h := by
  intro ε hε
  obtain ⟨g, hg, hhg⟩ := hh (ε / 2) (half_pos hε)
  obtain ⟨N, c, lam, θ, hN⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨N, c, lam, θ, fun x hx => ?_⟩
  have h1 := hhg x hx
  have h2 := hN x hx
  have heq : h x - ∑ i, c i * σ (lam i * x + θ i) =
      (h x - g x) + (g x - ∑ i, c i * σ (lam i * x + θ i)) := by ring
  rw [heq]
  calc |(h x - g x) + (g x - ∑ i, c i * σ (lam i * x + θ i))|
      ≤ |h x - g x| + |g x - ∑ i, c i * σ (lam i * x + θ i)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε

private lemma inSpanClosure_finset_sum {σ : ℝ → ℝ} {a b : ℝ} {ι : Type*}
    (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, InSpanClosure σ a b (f i)) :
    InSpanClosure σ a b (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inSpanClosure_zero σ a b
  | @insert i s hi ih =>
    have h1 := hf i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h3 := inSpanClosure_add h1 h2
    simpa [Finset.sum_insert hi] using h3

private lemma inSpanClosure_convolution {σ : ℝ → ℝ} (hσc : Continuous σ)
    {a b : ℝ} (φ : ContDiffBump (0 : ℝ)) (hR : φ.rOut ≤ 1) (lam θ : ℝ) :
    InSpanClosure σ a b
      (fun x => (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] σ) (lam * x + θ)) := by
  apply inSpanClosure_of_uniform_approx
  intro ε hε
  let ψ : ℝ → ℝ := φ.normed volume
  have hψ_cont : Continuous ψ := φ.continuous_normed
  have hconv_eq : ∀ y : ℝ, (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] σ) y =
      ∫ t in (-1 : ℝ)..1, ψ t * σ (y - t) := by
    intro y
    rw [MeasureTheory.convolution_def, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    symm
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    have hnot : t ∉ Metric.ball (0 : ℝ) φ.rOut := by
      intro hmem
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hmem
      exact ht ⟨by linarith, by linarith⟩
    have hψ0 : ψ t = 0 := by
      by_contra hne
      have : t ∈ Function.support ψ := hne
      rw [φ.support_normed_eq] at this
      exact hnot this
    simp [hψ0]
  let F : ℝ × ℝ → ℝ := fun p => ψ p.2 * σ (lam * p.1 + θ - p.2)
  have hF_cont : Continuous F := by
    have h1 : Continuous (fun p : ℝ × ℝ => ψ p.2) := hψ_cont.comp continuous_snd
    have h2 : Continuous (fun p : ℝ × ℝ => σ (lam * p.1 + θ - p.2)) :=
      hσc.comp (((continuous_const.mul continuous_fst).add continuous_const).sub continuous_snd)
    exact h1.mul h2
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hF_uc : UniformContinuousOn F (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1) :=
    hK.uniformContinuousOn_of_continuous hF_cont.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hF_uc (ε / 4) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / δ)
  let M' : ℕ := max M 1
  have hM'pos : 0 < M' := lt_of_lt_of_le Nat.zero_lt_one (le_max_right M 1)
  have hM'_rpos : (0 : ℝ) < M' := Nat.cast_pos.mpr hM'pos
  have hstep_lt : 2 / (M' : ℝ) < δ := by
    have h1 : 2 / δ < M' := hM.trans_le (Nat.cast_le.mpr (le_max_left M 1))
    rw [div_lt_iff₀ hM'_rpos]
    rw [div_lt_iff₀ hδpos] at h1
    linarith
  let pts : ℕ → ℝ := fun k => -1 + (k : ℝ) * (2 / M')
  let riemann : ℝ → ℝ := fun x =>
    ∑ k : Fin M', ((2 / (M' : ℝ)) * ψ (pts k.1)) * σ (lam * x + (θ - pts k.1))
  refine ⟨riemann, ?_, ?_⟩
  · refine inSpanClosure_finset_sum Finset.univ _ fun k _ => ?_
    exact inSpanClosure_smul _ (inSpanClosure_gen σ a b lam (θ - pts k.1))
  · intro x hx
    rw [hconv_eq (lam * x + θ)]
    have hpts0 : pts 0 = -1 := by simp [pts]
    have hptsM : pts M' = 1 := by
      simp only [pts]
      field_simp [hM'_rpos.ne']
      ring
    have hint_all : ∀ k : ℕ, IntervalIntegrable (fun t => F (x, t)) volume (pts k) (pts (k + 1)) := by
      intro k
      exact (hF_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hsplit : ∫ t in (-1 : ℝ)..1, F (x, t) =
        ∑ k ∈ Finset.range M', ∫ t in pts k..pts (k + 1), F (x, t) := by
      rw [← hpts0, ← hptsM]
      exact (intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hint_all k)).symm
    change |(∫ t in (-1 : ℝ)..1, F (x, t)) - riemann x| < ε
    rw [hsplit]
    have hriem_eq : riemann x =
        ∑ k ∈ Finset.range M', ∫ _t in pts k..pts (k + 1), F (x, pts k) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have hdiff : pts (k.1 + 1) - pts k.1 = 2 / M' := by
        simp only [pts]
        push_cast
        ring
      rw [hdiff]
      simp only [F]
      ring
    rw [hriem_eq, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.range M',
            ((∫ t in pts k..pts (k + 1), F (x, t)) -
              (∫ _t in pts k..pts (k + 1), F (x, pts k)))|
        ≤ ∑ k ∈ Finset.range M',
            |(∫ t in pts k..pts (k + 1), F (x, t)) -
              (∫ _t in pts k..pts (k + 1), F (x, pts k))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range M', (ε / 4) * (2 / M') := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < M' := Finset.mem_range.mp hk
          have hle : pts k ≤ pts (k + 1) := by
            simp only [pts]; push_cast
            have : 0 ≤ 2 / (M' : ℝ) := by positivity
            linarith
          rw [← intervalIntegral.integral_sub (hint_all k) intervalIntegrable_const]
          have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := pts k)
            (b := pts (k + 1)) (C := ε / 4) (f := fun t => F (x, t) - F (x, pts k))
            fun t ht => by
              rw [Set.uIoc_of_le hle] at ht
              have htk : pts k ∈ Set.Icc (-1 : ℝ) 1 := by
                simp only [pts, Set.mem_Icc]
                constructor
                · have : 0 ≤ (k : ℝ) * (2 / M') := by positivity
                  linarith
                · have hkM : (k : ℝ) ≤ M' := Nat.cast_le.mpr hk_lt.le
                  have h1 : (k : ℝ) * (2 / M') ≤ M' * (2 / M') := by gcongr
                  rw [mul_div_cancel₀ _ hM'_rpos.ne'] at h1
                  linarith
              have htk1 : pts (k + 1) ≤ 1 := by
                simp only [pts]
                have hkM : ((k + 1 : ℕ) : ℝ) ≤ M' := Nat.cast_le.mpr hk_lt
                have h1 : ((k + 1 : ℕ) : ℝ) * (2 / M') ≤ M' * (2 / M') := by gcongr
                rw [mul_div_cancel₀ _ hM'_rpos.ne'] at h1
                linarith
              have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨htk.1.trans ht.1.le, ht.2.trans htk1⟩
              have hdist : dist (x, t) (x, pts k) < δ := by
                rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq,
                  abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
                have hdiff : pts (k + 1) - pts k = 2 / M' := by simp only [pts]; push_cast; ring
                linarith [ht.2]
              have hlt := hδ (x, t) ⟨hx, ht_mem⟩ (x, pts k) ⟨hx, htk⟩ hdist
              simpa [Real.dist_eq, Real.norm_eq_abs] using hlt.le
          have hdiff : |pts (k + 1) - pts k| = 2 / M' := by
            have hd : pts (k + 1) - pts k = 2 / M' := by simp only [pts]; push_cast; ring
            rw [hd, abs_of_pos (by positivity)]
          simpa [Real.norm_eq_abs, hdiff] using hnorm
      _ = ε / 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [hM'_rpos.ne']
          ring
      _ < ε := by linarith

private lemma contDiff_infty_iteratedDeriv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k g) := by
  rw [iteratedDeriv_eq_iterate]
  exact hg.iterate_deriv k

private lemma inSpanClosure_pow_mul_iteratedDeriv {σ : ℝ → ℝ} {a b : ℝ} {g : ℝ → ℝ}
    (hg_smooth : ContDiff ℝ ∞ g)
    (hg_base : ∀ lam θ : ℝ, InSpanClosure σ a b (fun x => g (lam * x + θ))) :
    ∀ (k : ℕ) (lam θ : ℝ),
      InSpanClosure σ a b (fun x => x ^ k * iteratedDeriv k g (lam * x + θ)) := by
  intro k
  induction k with
  | zero =>
    intro lam θ
    simpa [iteratedDeriv_zero] using hg_base lam θ
  | succ k ih =>
    intro lam θ
    apply inSpanClosure_of_uniform_approx
    intro ε hε
    let G : ℝ → ℝ := iteratedDeriv k g
    have hG_smooth : ContDiff ℝ ∞ G := contDiff_infty_iteratedDeriv hg_smooth k
    have hG_deriv : ∀ y, HasDerivAt G (iteratedDeriv (k + 1) g y) y := by
      intro y
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp hG_smooth).1.differentiableAt.hasDerivAt
    have hG'_cont : Continuous (iteratedDeriv (k + 1) g) :=
      (contDiff_infty_iteratedDeriv hg_smooth (k + 1)).continuous
    let R : ℝ := max |a| |b| + 1
    have hRpos : 0 < R := by positivity
    have hxR : ∀ x ∈ Set.Icc a b, |x| ≤ R := by
      intro x hx
      have : |x| ≤ max |a| |b| := by
        rw [abs_le]
        constructor
        · have := neg_abs_le a
          have := le_max_left |a| |b|
          linarith [hx.1]
        · have := le_abs_self b
          have := le_max_right |a| |b|
          linarith [hx.2]
      linarith
    let B : ℝ := |lam| * R + |θ| + R
    have huc : UniformContinuousOn (iteratedDeriv (k + 1) g) (Set.Icc (-B) B) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hG'_cont.continuousOn
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.uniformContinuousOn_iff.mp huc (ε / (R ^ (k + 1) + 1)) (by positivity)
    let h : ℝ := min 1 (δ / (2 * R))
    have hhpos : 0 < h := lt_min zero_lt_one (by positivity)
    have hh_le1 : h ≤ 1 := min_le_left _ _
    have hhR : h * R < δ := by
      have h1 : h ≤ δ / (2 * R) := min_le_right _ _
      have h2 : h * R ≤ (δ / (2 * R)) * R := by gcongr
      have h3 : (δ / (2 * R)) * R = δ / 2 := by field_simp [hRpos.ne']
      linarith
    let Q : ℝ → ℝ := fun x =>
      h⁻¹ * (x ^ k * G ((lam + h) * x + θ) - x ^ k * G (lam * x + θ))
    refine ⟨Q, inSpanClosure_smul h⁻¹ (inSpanClosure_sub (ih (lam + h) θ) (ih lam θ)), ?_⟩
    intro x hx
    have hx_le : |x| ≤ R := hxR x hx
    by_cases hx0 : x = 0
    · simp only [hx0, zero_pow (Nat.succ_ne_zero k), zero_mul, Q, sub_self, mul_zero, abs_zero]
      exact hε
    · let u₀ : ℝ := lam * x + θ
      let u₁ : ℝ := (lam + h) * x + θ
      have hu_diff : u₁ - u₀ = h * x := by dsimp [u₀, u₁]; ring
      have hu_ne : u₀ ≠ u₁ := by
        intro heq
        have : h * x = 0 := by linarith [hu_diff]
        exact (mul_ne_zero hhpos.ne' hx0) this
      have hmvt : ∃ ξ ∈ Set.uIcc u₀ u₁, G u₁ - G u₀ = iteratedDeriv (k + 1) g ξ * (u₁ - u₀) := by
        rcases lt_or_gt_of_ne hu_ne with hlt | hgt
        · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope G (iteratedDeriv (k + 1) g) hlt
            hG_smooth.continuous.continuousOn (fun y _ => hG_deriv y)
          refine ⟨ξ, Set.Ioo_subset_Icc_self hξ |> Set.Icc_subset_uIcc, ?_⟩
          have hne : u₁ - u₀ ≠ 0 := (sub_pos.mpr hlt).ne'
          field_simp [hne] at hslope
          linarith
        · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope G (iteratedDeriv (k + 1) g) hgt
            hG_smooth.continuous.continuousOn (fun y _ => hG_deriv y)
          refine ⟨ξ, ?_, ?_⟩
          · rw [Set.uIcc_comm]
            exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hξ)
          · have hne : u₀ - u₁ ≠ 0 := (sub_pos.mpr hgt).ne'
            field_simp [hne] at hslope
            linarith
      obtain ⟨ξ, hξ, hξ_eq⟩ := hmvt
      have hQ_eq : Q x = x ^ (k + 1) * iteratedDeriv (k + 1) g ξ := by
        dsimp only [Q]
        rw [← mul_sub, hξ_eq, hu_diff]
        field_simp [hhpos.ne']
        ring
      rw [hQ_eq, ← mul_sub, abs_mul]
      have hu₀_mem : u₀ ∈ Set.Icc (-B) B := by
        refine abs_le.mp ?_
        calc |lam * x + θ| ≤ |lam * x| + |θ| := abs_add_le _ _
          _ = |lam| * |x| + |θ| := by rw [abs_mul]
          _ ≤ |lam| * R + |θ| := by gcongr
          _ ≤ B := by dsimp [B]; linarith
      have hu₁_mem : u₁ ∈ Set.Icc (-B) B := by
        refine abs_le.mp ?_
        have : u₁ = u₀ + h * x := by dsimp [u₀, u₁]; ring
        rw [this]
        calc |u₀ + h * x| ≤ |u₀| + |h * x| := abs_add_le _ _
          _ = |u₀| + h * |x| := by rw [abs_mul, abs_of_pos hhpos]
          _ ≤ (|lam| * R + |θ|) + 1 * R := by
              have hu₀b : |u₀| ≤ |lam| * R + |θ| := by
                calc |lam * x + θ| ≤ |lam| * |x| + |θ| := by
                      rw [← abs_mul]; exact abs_add_le _ _
                  _ ≤ |lam| * R + |θ| := by gcongr
              have hhx : h * |x| ≤ 1 * R := mul_le_mul hh_le1 hx_le (abs_nonneg _) zero_le_one
              linarith
          _ = B := by dsimp [B]; ring
      have hξ_mem : ξ ∈ Set.Icc (-B) B :=
        (Set.uIcc_subset_Icc hu₀_mem hu₁_mem) hξ
      have hξ_dist : dist u₀ ξ < δ := by
        rw [Real.dist_eq]
        have hle : |ξ - u₀| ≤ |u₁ - u₀| := by
          rcases Set.mem_uIcc.mp hξ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg (sub_nonneg.mpr (h1.trans h2))]
            linarith
          · rw [abs_sub_comm ξ u₀, abs_of_nonneg (sub_nonneg.mpr h2),
              abs_sub_comm u₁ u₀, abs_of_nonneg (sub_nonneg.mpr (h1.trans h2))]
            linarith
        rw [abs_sub_comm]
        calc |ξ - u₀| ≤ |u₁ - u₀| := hle
          _ = h * |x| := by rw [hu_diff, abs_mul, abs_of_pos hhpos]
          _ ≤ h * R := by gcongr
          _ < δ := hhR
      have hdiff_lt := hδ u₀ hu₀_mem ξ hξ_mem hξ_dist
      rw [Real.dist_eq] at hdiff_lt
      have hxpow : |x ^ (k + 1)| ≤ R ^ (k + 1) := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hx_le _
      have hden_pos : 0 < R ^ (k + 1) + 1 := by positivity
      calc |x ^ (k + 1)| * |iteratedDeriv (k + 1) g u₀ - iteratedDeriv (k + 1) g ξ|
          ≤ R ^ (k + 1) * (ε / (R ^ (k + 1) + 1)) := by gcongr
        _ < (R ^ (k + 1) + 1) * (ε / (R ^ (k + 1) + 1)) := by
            have : 0 < ε / (R ^ (k + 1) + 1) := by positivity
            nlinarith
        _ = ε := by field_simp [hden_pos.ne']

private lemma degree_sum_lt_of_forall_lt {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ)
    (n : ℕ) (hf : ∀ i ∈ s, (f i).degree < (n : WithBot ℕ)) :
    (∑ i ∈ s, f i).degree < (n : WithBot ℕ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe n
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private lemma eq_poly_of_iteratedDeriv_eq_zero :
    ∀ (k : ℕ) (h : ℝ → ℝ), ContDiff ℝ ∞ h → (∀ x, iteratedDeriv k h x = 0) →
      ∃ P : Polynomial ℝ, P.degree < k ∧ ∀ x, h x = P.eval x := by
  intro k
  induction k with
  | zero =>
    intro h _ hk
    refine ⟨0, by simp, fun x => ?_⟩
    simpa [iteratedDeriv_zero] using hk x
  | succ k ih =>
    intro h hh hk
    have hderiv_smooth : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
    have hderiv_zero : ∀ x, iteratedDeriv k (deriv h) x = 0 := by
      intro x
      rw [← iteratedDeriv_succ']
      exact hk x
    obtain ⟨Q, hQdeg, hQeval⟩ := ih (deriv h) hderiv_smooth hderiv_zero
    let P : Polynomial ℝ :=
      Polynomial.C (h 0) +
        ∑ i ∈ Q.support, Polynomial.C (Q.coeff i / ((i : ℝ) + 1)) * Polynomial.X ^ (i + 1)
    have hPderiv : P.derivative = Q := by
      dsimp only [P]
      rw [Polynomial.derivative_add, Polynomial.derivative_C, zero_add, map_sum]
      conv_rhs => rw [Q.as_sum_support_C_mul_X_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
        Polynomial.derivative_X_pow, ← mul_assoc, ← Polynomial.C_mul, Nat.add_sub_cancel]
      have hne : ((i : ℝ) + 1) ≠ 0 := by positivity
      congr 2
      push_cast
      field_simp [hne]
    have hPdeg : P.degree < (k + 1 : ℕ) := by
      dsimp only [P]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (WithBot.coe_lt_coe.mpr (Nat.succ_pos k))
      · refine degree_sum_lt_of_forall_lt Q.support _ (k + 1) fun i hi => ?_
        have hi_lt : i < k := by
          have h1 : (i : WithBot ℕ) ≤ Q.degree := Polynomial.le_degree_of_mem_supp i hi
          have h2 : (i : WithBot ℕ) < (k : WithBot ℕ) := lt_of_le_of_lt h1 hQdeg
          exact WithBot.coe_lt_coe.mp h2
        calc (Polynomial.C (Q.coeff i / ((i : ℝ) + 1)) * Polynomial.X ^ (i + 1)).degree
            ≤ (Polynomial.C (Q.coeff i / ((i : ℝ) + 1))).degree + (Polynomial.X ^ (i + 1)).degree :=
              Polynomial.degree_mul_le _ _
          _ ≤ 0 + (i + 1 : ℕ) := by
              rw [Polynomial.degree_X_pow]
              exact add_le_add Polynomial.degree_C_le le_rfl
          _ = (i + 1 : ℕ) := zero_add _
          _ < (k + 1 : ℕ) := WithBot.coe_lt_coe.mpr (Nat.succ_lt_succ hi_lt)
    have hP0 : P.eval 0 = h 0 := by
      simp [P, Polynomial.eval_finsetSum]
    have hdiff_deriv : ∀ x, deriv (fun y => h y - P.eval y) x = 0 := by
      intro x
      have h1 : HasDerivAt h (deriv h x) x := (contDiff_infty_iff_deriv.mp hh).1.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun y => P.eval y) (P.derivative.eval x) x := P.hasDerivAt x
      change deriv (h - fun y => P.eval y) x = 0
      rw [(h1.sub h2).deriv, hPderiv, hQeval x, sub_self]
    have hconst := is_const_of_deriv_eq_zero
      ((contDiff_infty_iff_deriv.mp hh).1.sub P.differentiable) hdiff_deriv
    refine ⟨P, hPdeg, fun x => ?_⟩
    have hx0 : h x - P.eval x = h 0 - P.eval 0 := hconst x 0
    linarith [hP0]

private lemma continuous_not_poly_isTauberWiener (σ : ℝ → ℝ) (hσc : Continuous σ)
    (hσp : ¬ IsPolynomialFun σ) : IsTauberWiener σ := by
  intro a b f hf ε hε
  let φ (n : ℕ) : ContDiffBump (0 : ℝ) :=
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) hn]
      linarith⟩
  let g (n : ℕ) : ℝ → ℝ := φ n |>.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] σ
  have hg_smooth : ∀ n, ContDiff ℝ ∞ (g n) := fun n =>
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ n).contDiff_normed hσc.locallyIntegrable
  have hg_tend : ∀ y : ℝ, Tendsto (fun n => g n y) atTop (𝓝 (σ y)) := by
    intro y
    refine ContDiffBump.convolution_tendsto_right_of_continuous (φ := φ) ?_ hσc y
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hex_nonzero : ∀ k : ℕ, ∃ (n : ℕ) (θ : ℝ), iteratedDeriv k (g n) θ ≠ 0 := by
    intro k
    by_contra hall
    push Not at hall
    have hpoly : ∀ n : ℕ, ∃ P : Polynomial ℝ, P.degree < k ∧ ∀ y, g n y = P.eval y :=
      fun n => eq_poly_of_iteratedDeriv_eq_zero k (g n) (hg_smooth n) (hall n)
    choose Pn hPn_deg hPn_eval using hpoly
    let v : Fin k → ℝ := fun i => (i : ℝ)
    have hv_inj : Set.InjOn v (Finset.univ : Finset (Fin k)) := by
      intro i _ j _ hij
      exact Fin.ext (Nat.cast_injective hij)
    let Q : Polynomial ℝ := Lagrange.interpolate Finset.univ v (fun i => σ (v i))
    have hσ_eq_Q : ∀ y : ℝ, σ y = Q.eval y := by
      intro y
      have hgn_eq : ∀ n : ℕ,
          g n y = ∑ i : Fin k, g n (v i) * (Lagrange.basis Finset.univ v i).eval y := by
        intro n
        have hdeg : (Pn n).degree < (Finset.univ : Finset (Fin k)).card := by
          simpa using hPn_deg n
        have hinterp := Lagrange.eq_interpolate hv_inj hdeg
        rw [hPn_eval n y]
        conv_lhs => rw [hinterp]
        simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, ← hPn_eval n]
      have htend_rhs : Tendsto (fun n =>
          ∑ i : Fin k, g n (v i) * (Lagrange.basis Finset.univ v i).eval y) atTop
          (𝓝 (∑ i : Fin k, σ (v i) * (Lagrange.basis Finset.univ v i).eval y)) :=
        tendsto_finsetSum _ fun i _ => (hg_tend (v i)).mul_const _
      have htend_lhs : Tendsto (fun n => g n y) atTop
          (𝓝 (∑ i : Fin k, σ (v i) * (Lagrange.basis Finset.univ v i).eval y)) :=
        htend_rhs.congr fun n => (hgn_eq n).symm
      have heq := tendsto_nhds_unique (hg_tend y) htend_lhs
      simpa [Q, Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C] using heq
    exact hσp ⟨Q, hσ_eq_Q⟩
  have hmono : ∀ k : ℕ, InSpanClosure σ a b (fun x => x ^ k) := by
    intro k
    obtain ⟨n, θ, hne⟩ := hex_nonzero k
    have hR : (φ n).rOut ≤ 1 := by
      dsimp only [φ]
      rw [div_le_one (by positivity)]
      linarith
    have hbase : ∀ lam θ' : ℝ, InSpanClosure σ a b (fun x => g n (lam * x + θ')) :=
      fun lam θ' => inSpanClosure_convolution hσc (φ n) hR lam θ'
    have hk := inSpanClosure_pow_mul_iteratedDeriv (hg_smooth n) hbase k 0 θ
    have hscaled := inSpanClosure_smul (iteratedDeriv k (g n) θ)⁻¹ hk
    have heq : (fun x : ℝ => (iteratedDeriv k (g n) θ)⁻¹ * (x ^ k * iteratedDeriv k (g n) (0 * x + θ))) =
        fun x => x ^ k := by
      ext x
      simp only [zero_mul, zero_add]
      field_simp [hne]
    rwa [heq] at hscaled
  have hpoly_in : ∀ P : Polynomial ℝ, InSpanClosure σ a b (fun x => P.eval x) := by
    intro P
    have heq : (fun x => P.eval x) = fun x => ∑ i ∈ P.support, P.coeff i * x ^ i := by
      ext x
      rw [Polynomial.eval_eq_sum]
      rfl
    rw [heq]
    refine inSpanClosure_finset_sum P.support _ fun i _ => ?_
    exact inSpanClosure_smul (P.coeff i) (hmono i)
  have hf_in : InSpanClosure σ a b f := by
    apply inSpanClosure_of_uniform_approx
    intro δ hδ
    obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn a b f hf δ hδ
    refine ⟨fun x => P.eval x, hpoly_in P, fun x hx => ?_⟩
    rw [abs_sub_comm]
    exact hP x hx
  exact hf_in ε hε

/-! ### Part 2: Finite-dimensional UAT on compact subsets of ℝ^q -/

private lemma uat_fin_scalar {q : ℕ} (σ : ℝ → ℝ) (hσ : IsTauberWiener σ)
    (S : Set (Fin q → ℝ)) (hS : IsCompact S) (F : (Fin q → ℝ) → ℝ) (hF : ContinuousOn F S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c b : Fin n → ℝ) (W : Fin n → Fin q → ℝ),
      ∀ v ∈ S, |F v - ∑ i : Fin n, c i * σ (∑ j : Fin q, W i j * v j + b i)| < ε := by
  by_cases hSne : S.Nonempty
  · have : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS
    have : Nonempty ↥S := hSne.to_subtype
    let gen (w : Fin q → ℝ) : C(↥S, ℝ) :=
      ⟨fun v => Real.exp (∑ j : Fin q, w j * v.1 j),
        Real.continuous_exp.comp (continuous_finsetSum _ fun j _ =>
          continuous_const.mul ((continuous_apply j).comp continuous_subtype_val))⟩
    have hgen_zero : gen 0 = 1 := by ext v; simp [gen]
    have hgen_mul : ∀ w₁ w₂ : Fin q → ℝ, gen w₁ * gen w₂ = gen (w₁ + w₂) := by
      intro w₁ w₂
      ext v
      simp only [ContinuousMap.mul_apply, gen, ContinuousMap.coe_mk, ← Real.exp_add,
        ← Finset.sum_add_distrib]
      congr 2
      ext j
      simp [add_mul]
    let Sspan : Submodule ℝ C(↥S, ℝ) := Submodule.span ℝ (Set.range gen)
    let A : Subalgebra ℝ C(↥S, ℝ) :=
      { carrier := Sspan
        mul_mem' := by
          intro g₁ g₂ hg₁ hg₂
          change g₁ ∈ Sspan at hg₁; change g₂ ∈ Sspan at hg₂; change g₁ * g₂ ∈ Sspan
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hg₁
          · rintro _ ⟨w₁, rfl⟩
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hg₂
            · rintro _ ⟨w₂, rfl⟩
              rw [hgen_mul]
              exact Submodule.subset_span ⟨w₁ + w₂, rfl⟩
            · rw [mul_zero]; exact Sspan.zero_mem
            · intro a b _ _ ha hb; rw [mul_add]; exact Sspan.add_mem ha hb
            · intro r a _ ha; rw [mul_smul_comm]; exact Sspan.smul_mem r ha
          · rw [zero_mul]; exact Sspan.zero_mem
          · intro a b _ _ ha hb; rw [add_mul]; exact Sspan.add_mem ha hb
          · intro r a _ ha; rw [smul_mul_assoc]; exact Sspan.smul_mem r ha
        one_mem' := by
          change (1 : C(↥S, ℝ)) ∈ Sspan
          rw [← hgen_zero]
          exact Submodule.subset_span ⟨0, rfl⟩
        add_mem' := fun ha hb => Sspan.add_mem ha hb
        zero_mem' := Sspan.zero_mem
        algebraMap_mem' := fun r => by
          change algebraMap ℝ C(↥S, ℝ) r ∈ Sspan
          rw [Algebra.algebraMap_eq_smul_one]
          refine Sspan.smul_mem r ?_
          rw [← hgen_zero]
          exact Submodule.subset_span ⟨0, rfl⟩ }
    have hAsep : A.SeparatesPoints := by
      intro v₁ v₂ hne
      have hval : v₁.1 ≠ v₂.1 := fun h => hne (Subtype.ext h)
      have hexj : ∃ j : Fin q, v₁.1 j ≠ v₂.1 j := by
        by_contra hall
        push Not at hall
        exact hval (funext hall)
      obtain ⟨j, hj⟩ := hexj
      let w : Fin q → ℝ := Pi.single j 1
      refine ⟨gen w, ⟨gen w, Submodule.subset_span ⟨w, rfl⟩, rfl⟩, ?_⟩
      simp only [gen, ContinuousMap.coe_mk, w, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact fun h => hj (Real.exp_injective h)
    obtain ⟨⟨g, hgA⟩, hg_approx⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hAsep
        (fun v : ↥S => F v.1) hF.domRestrict (ε / 2) (half_pos hε)
    have hg_span : g ∈ Submodule.span ℝ (Set.range gen) := hgA
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hg_span
    obtain ⟨coeff, hcoeff⟩ := hg_span
    let M : ℕ := coeff.support.card
    let eM : Fin M ≃ coeff.support := coeff.support.equivFin.symm
    let a : Fin M → ℝ := fun s => coeff (eM s).1
    let ws : Fin M → Fin q → ℝ := fun s => (eM s).1
    have hg_eq : ∀ v : ↥S, g v = ∑ s : Fin M, a s * Real.exp (∑ j : Fin q, ws s j * v.1 j) := by
      intro v
      rw [← hcoeff]
      simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
        smul_eq_mul]
      rw [← Finset.sum_coe_sort coeff.support]
      rw [← Equiv.sum_comp eM]
      rfl
    by_cases hM : M = 0
    · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun v hvS => ?_⟩
      have hgv : g ⟨v, hvS⟩ = 0 := by
        rw [hg_eq ⟨v, hvS⟩]
        exact Finset.sum_eq_zero fun s _ => absurd s.2 (by omega)
      have h1 : |g ⟨v, hvS⟩ - F v| < ε / 2 := by
        simpa [Real.norm_eq_abs] using hg_approx ⟨v, hvS⟩
      rw [hgv, zero_sub, abs_neg] at h1
      simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
      linarith
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
      have hM_rpos : (0 : ℝ) < M := Nat.cast_pos.mpr hMpos
      have happrox_s : ∀ s : Fin M,
          ∃ (Ns : ℕ) (cs lams θs : Fin Ns → ℝ),
            ∀ v ∈ S, |Real.exp (∑ j : Fin q, ws s j * v j) -
              ∑ i : Fin Ns, cs i * σ (lams i * (∑ j : Fin q, ws s j * v j) + θs i)| <
              ε / (2 * M * (|a s| + 1)) := by
        intro s
        let Ls : C(↥S, ℝ) :=
          ⟨fun v => ∑ j : Fin q, ws s j * v.1 j,
            continuous_finsetSum _ fun j _ =>
              continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)⟩
        let R : ℝ := ‖Ls‖
        have hδpos : 0 < ε / (2 * M * (|a s| + 1)) := by positivity
        obtain ⟨Ns, cs, lams, θs, hNs⟩ :=
          hσ (-R) R Real.exp Real.continuous_exp.continuousOn _ hδpos
        refine ⟨Ns, cs, lams, θs, fun v hvS => ?_⟩
        exact hNs _ (abs_le.mp (ContinuousMap.norm_coe_le_norm Ls ⟨v, hvS⟩))
      choose Ns cs lams θs hNs using happrox_s
      let Idx := Σ s : Fin M, Fin (Ns s)
      let n : ℕ := Fintype.card Idx
      let eIdx : Fin n ≃ Idx := (Fintype.equivFin Idx).symm
      let c_all : Fin n → ℝ := fun k => a (eIdx k).1 * cs (eIdx k).1 (eIdx k).2
      let b_all : Fin n → ℝ := fun k => θs (eIdx k).1 (eIdx k).2
      let W_all : Fin n → Fin q → ℝ := fun k j => lams (eIdx k).1 (eIdx k).2 * ws (eIdx k).1 j
      refine ⟨n, c_all, b_all, W_all, fun v hvS => ?_⟩
      have hnet : (∑ k : Fin n, c_all k * σ (∑ j : Fin q, W_all k j * v j + b_all k)) =
          ∑ s : Fin M, a s * ∑ i : Fin (Ns s),
            cs s i * σ (lams s i * (∑ j : Fin q, ws s j * v j) + θs s i) := by
        have h1 : (∑ k : Fin n, c_all k * σ (∑ j : Fin q, W_all k j * v j + b_all k)) =
            ∑ p : Idx, a p.1 * (cs p.1 p.2 *
              σ (lams p.1 p.2 * (∑ j : Fin q, ws p.1 j * v j) + θs p.1 p.2)) := by
          rw [← Equiv.sum_comp eIdx]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [c_all, b_all, W_all, mul_assoc]
          congr 3
          rw [Finset.mul_sum]
        rw [h1, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      have h1 : |F v - g ⟨v, hvS⟩| < ε / 2 := by
        have := hg_approx ⟨v, hvS⟩
        rw [Real.norm_eq_abs, abs_sub_comm] at this
        exact this
      have h2 : |g ⟨v, hvS⟩ - ∑ k : Fin n, c_all k * σ (∑ j : Fin q, W_all k j * v j + b_all k)| < ε / 2 := by
        rw [hg_eq ⟨v, hvS⟩, hnet, ← Finset.sum_sub_distrib]
        calc |∑ s : Fin M, (a s * Real.exp (∑ j, ws s j * v j) -
                a s * ∑ i : Fin (Ns s), cs s i * σ (lams s i * (∑ j, ws s j * v j) + θs s i))|
            ≤ ∑ s : Fin M, |a s * Real.exp (∑ j, ws s j * v j) -
                a s * ∑ i : Fin (Ns s), cs s i * σ (lams s i * (∑ j, ws s j * v j) + θs s i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ < ∑ _s : Fin M, ε / (2 * M) := by
              refine Finset.sum_lt_sum_of_nonempty
                (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hMpos)) fun s _ => ?_
              rw [← mul_sub, abs_mul]
              have hlt := hNs s v hvS
              have ha_pos : 0 < |a s| + 1 := by positivity
              calc |a s| * |Real.exp (∑ j, ws s j * v j) -
                      ∑ i : Fin (Ns s), cs s i * σ (lams s i * (∑ j, ws s j * v j) + θs s i)|
                  ≤ |a s| * (ε / (2 * M * (|a s| + 1))) := by gcongr
                _ < (|a s| + 1) * (ε / (2 * M * (|a s| + 1))) := by
                    have : 0 < ε / (2 * M * (|a s| + 1)) := by positivity
                    nlinarith
                _ = ε / (2 * M) := by field_simp [ha_pos.ne', hM_rpos.ne']
          _ = ε / 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp [hM_rpos.ne']
      have hsplit : F v - ∑ k : Fin n, c_all k * σ (∑ j, W_all k j * v j + b_all k) =
          (F v - g ⟨v, hvS⟩) + (g ⟨v, hvS⟩ - ∑ k : Fin n, c_all k * σ (∑ j, W_all k j * v j + b_all k)) := by
        ring
      rw [hsplit]
      linarith [abs_add_le (F v - g ⟨v, hvS⟩)
        (g ⟨v, hvS⟩ - ∑ k : Fin n, c_all k * σ (∑ j, W_all k j * v j + b_all k))]
  · rw [Set.not_nonempty_iff_eq_empty] at hSne
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun v hv => by rw [hSne] at hv; exact hv.elim⟩

/-! ### Part 3: Euclidean norm, interpolation operator, and Gronwall inequality -/

private lemma eucNorm_nonneg {K : ℕ} (v : Fin K → ℝ) : 0 ≤ eucNorm v :=
  Real.sqrt_nonneg _

private lemma eucNorm_sq {K : ℕ} (v : Fin K → ℝ) : eucNorm v ^ 2 = ∑ i : Fin K, v i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma dot_le_eucNorm_mul {K : ℕ} (u v : Fin K → ℝ) :
    ∑ i : Fin K, u i * v i ≤ eucNorm u * eucNorm v := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have hprod : (∑ i : Fin K, u i ^ 2) * (∑ i : Fin K, v i ^ 2) = (eucNorm u * eucNorm v) ^ 2 := by
    rw [mul_pow, eucNorm_sq, eucNorm_sq]
  rw [hprod] at hcs
  have hnonneg : 0 ≤ eucNorm u * eucNorm v := mul_nonneg (eucNorm_nonneg u) (eucNorm_nonneg v)
  have habs : |∑ i : Fin K, u i * v i| ≤ eucNorm u * eucNorm v := by
    rw [← abs_of_nonneg hnonneg]
    exact sq_le_sq.mp hcs
  exact (le_abs_self _).trans habs

private lemma eucNorm_add_le {K : ℕ} (u v : Fin K → ℝ) :
    eucNorm (u + v) ≤ eucNorm u + eucNorm v := by
  have hnonneg : 0 ≤ eucNorm u + eucNorm v := add_nonneg (eucNorm_nonneg u) (eucNorm_nonneg v)
  have hsq : eucNorm (u + v) ^ 2 ≤ (eucNorm u + eucNorm v) ^ 2 := by
    rw [eucNorm_sq]
    have hexp : ∑ i : Fin K, (u i + v i) ^ 2 =
        (∑ i : Fin K, u i ^ 2) + 2 * (∑ i : Fin K, u i * v i) + ∑ i : Fin K, v i ^ 2 := by
      simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    change ∑ i : Fin K, (u i + v i) ^ 2 ≤ (eucNorm u + eucNorm v) ^ 2
    rw [hexp, ← eucNorm_sq u, ← eucNorm_sq v]
    have hdot := dot_le_eucNorm_mul u v
    nlinarith
  have habs : |eucNorm (u + v)| ≤ |eucNorm u + eucNorm v| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (eucNorm_nonneg _), abs_of_nonneg hnonneg] at habs

private lemma eucNorm_sub_triangle {K : ℕ} (u v w : Fin K → ℝ) :
    eucNorm (u - w) ≤ eucNorm (u - v) + eucNorm (v - w) := by
  have heq : u - w = (u - v) + (v - w) := by ext i; simp
  rw [heq]
  exact eucNorm_add_le (u - v) (v - w)

private lemma continuous_eucNorm {K : ℕ} : Continuous (eucNorm (K := K)) := by
  unfold eucNorm
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  exact (continuous_apply i).pow 2

private lemma sensor_mem_Icc'' {a b : ℝ} (hab : a < b) {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    sensor a b m j ∈ Set.Icc a b := by
  unfold sensor
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hba : 0 < b - a := sub_pos.mpr hab
  have hj_le : (j : ℝ) ≤ m := Nat.cast_le.mpr hj
  constructor
  · have : 0 ≤ (j : ℝ) * (b - a) / m := by positivity
    linarith
  · have h1 : (j : ℝ) * (b - a) / m ≤ m * (b - a) / m := by gcongr
    rw [mul_div_cancel_left₀ _ hm_pos.ne'] at h1
    linarith

private lemma sensor_succ_sub'' (a b : ℝ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    sensor a b m (j + 1) - sensor a b m j = (b - a) / m := by
  unfold sensor
  push_cast
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp
  ring

private lemma sensor_zero'' (a b : ℝ) (m : ℕ) : sensor a b m 0 = a := by simp [sensor]

private lemma sensor_self'' (a b : ℝ) {m : ℕ} (hm : 0 < m) : sensor a b m m = b := by
  unfold sensor
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [mul_div_cancel_left₀ _ hm_ne]
  ring

private lemma sensor_mono'' {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) {i j : ℕ} (hij : i ≤ j) :
    sensor a b m i ≤ sensor a b m j := by
  unfold sensor
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hba : 0 < b - a := sub_pos.mpr hab
  have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  gcongr

-- Piecewise-linear interpolant directly from a vector of sensor values v : Fin (m + 1) → ℝ
private noncomputable def interpVecFun (a b : ℝ) (m : ℕ) (v : Fin (m + 1) → ℝ) (x : ℝ) : ℝ :=
  let j : ℕ := min ⌊(x - a) * m / (b - a)⌋₊ (m - 1)
  if hj : j + 1 ≤ m then
    v ⟨j, by omega⟩ + (v ⟨j + 1, by omega⟩ - v ⟨j, by omega⟩) /
      (sensor a b m (j + 1) - sensor a b m j) * (x - sensor a b m j)
  else 0

private lemma interpVecFun_sensorValues {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (u : C(Set.Icc a b, ℝ)) (x : ℝ) :
    interpVecFun a b m (sensorValues a b m u) x = interp a b m (evalAt u) x := by
  unfold interpVecFun interp sensorValues
  dsimp only
  have hj : min ⌊(x - a) * m / (b - a)⌋₊ (m - 1) + 1 ≤ m := by
    have : min ⌊(x - a) * m / (b - a)⌋₊ (m - 1) ≤ m - 1 := min_le_right _ _
    omega
  rw [dif_pos hj]

private lemma interpVecFun_eq_affine_on_seg {a b : ℝ} (hab : a < b) {m j : ℕ} (hm : 0 < m)
    (hj : j < m) (v : Fin (m + 1) → ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (sensor a b m j) (sensor a b m (j + 1))) :
    interpVecFun a b m v x =
      v ⟨j, by omega⟩ +
        (v ⟨j + 1, by omega⟩ - v ⟨j, by omega⟩) /
          (sensor a b m (j + 1) - sensor a b m j) * (x - sensor a b m j) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hstep : sensor a b m (j + 1) - sensor a b m j ≠ 0 := by
    rw [sensor_succ_sub'' a b hm j]
    exact (div_pos hba hm_pos).ne'
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · have ht : (sensor a b m (j + 1) - a) * m / (b - a) = (j + 1 : ℕ) := by
      unfold sensor; push_cast; field_simp [hba.ne', hm_pos.ne']; ring
    have hfl : ⌊(sensor a b m (j + 1) - a) * m / (b - a)⌋₊ = j + 1 := by
      rw [ht, Nat.floor_natCast]
    by_cases hj1 : j + 1 < m
    · have hmin : min ⌊(sensor a b m (j + 1) - a) * m / (b - a)⌋₊ (m - 1) = j + 1 := by
        rw [hfl]; exact min_eq_left (by omega)
      unfold interpVecFun
      dsimp only
      simp only [hmin]
      have hj1' : j + 1 + 1 ≤ m := by omega
      rw [dif_pos hj1', sub_self, mul_zero, add_zero]
      field_simp [hstep]
      ring
    · have hjm : j = m - 1 := by omega
      have hmin : min ⌊(sensor a b m (j + 1) - a) * m / (b - a)⌋₊ (m - 1) = j := by
        rw [hfl, hjm]; exact min_eq_right (by omega)
      unfold interpVecFun
      dsimp only
      simp only [hmin]
      rw [dif_pos (by omega : j + 1 ≤ m)]
  · set t : ℝ := (x - a) * m / (b - a)
    have ht_lo : (j : ℝ) ≤ t := by
      dsimp [t]; rw [le_div_iff₀ hba]
      have h1 : sensor a b m j ≤ x := hx.1
      unfold sensor at h1
      have h2 : (j : ℝ) * (b - a) / m ≤ x - a := by linarith
      have h3 : (j : ℝ) * (b - a) / m * m ≤ (x - a) * m := by gcongr
      rwa [div_mul_cancel₀ _ hm_pos.ne'] at h3
    have ht_hi : t < (j : ℝ) + 1 := by
      dsimp [t]; rw [div_lt_iff₀ hba]
      have h1 : x < sensor a b m (j + 1) := hlt
      unfold sensor at h1; push_cast at h1
      have h2 : x - a < ((j : ℝ) + 1) * (b - a) / m := by linarith
      have h3 : (x - a) * m < ((j : ℝ) + 1) * (b - a) / m * m := by gcongr
      rwa [div_mul_cancel₀ _ hm_pos.ne'] at h3
    have hfl : ⌊t⌋₊ = j := by
      rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg j) ht_lo)]
      exact ⟨ht_lo, ht_hi⟩
    have hmin : min ⌊(x - a) * m / (b - a)⌋₊ (m - 1) = j := by
      change min ⌊t⌋₊ (m - 1) = j
      rw [hfl]; exact min_eq_left (by omega)
    unfold interpVecFun
    dsimp only
    simp only [hmin]
    rw [dif_pos (by omega : j + 1 ≤ m)]

private lemma continuousOn_interpVecFun {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (v : Fin (m + 1) → ℝ) : ContinuousOn (interpVecFun a b m v) (Set.Icc a b) := by
  suffices ∀ k ≤ m, ContinuousOn (interpVecFun a b m v) (Set.Icc a (sensor a b m k)) by
    simpa [sensor_self'' a b hm] using this m le_rfl
  intro k hk
  induction k with
  | zero =>
    rw [sensor_zero'', Set.Icc_self]
    exact continuousOn_singleton _ _
  | succ k ih =>
    have hprev := ih (Nat.le_of_succ_le hk)
    have hseg : ContinuousOn (interpVecFun a b m v)
        (Set.Icc (sensor a b m k) (sensor a b m (k + 1))) := by
      have hcont : Continuous fun x : ℝ =>
          v ⟨k, by omega⟩ +
            (v ⟨k + 1, by omega⟩ - v ⟨k, by omega⟩) /
              (sensor a b m (k + 1) - sensor a b m k) * (x - sensor a b m k) := by fun_prop
      exact hcont.continuousOn.congr fun x hx => interpVecFun_eq_affine_on_seg hab hm hk v hx
    have hunion : Set.Icc a (sensor a b m (k + 1)) =
        Set.Icc a (sensor a b m k) ∪ Set.Icc (sensor a b m k) (sensor a b m (k + 1)) := by
      rw [Set.Icc_union_Icc_eq_Icc]
      · simpa [sensor_zero''] using sensor_mono'' hab hm (Nat.zero_le k)
      · exact sensor_mono'' hab hm (Nat.le_succ k)
    rw [hunion]
    exact hprev.union_of_isClosed hseg isClosed_Icc isClosed_Icc

private noncomputable def interpVec {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (v : Fin (m + 1) → ℝ) : C(Set.Icc a b, ℝ) :=
  ⟨fun x => interpVecFun a b m v x.1,
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_interpVecFun hab hm v)⟩

private lemma interpVec_continuous {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m) :
    Continuous (interpVec hab hm) := by
  rw [Metric.continuous_iff]
  intro v ε hε
  refine ⟨ε, hε, fun w hvw => ?_⟩
  rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
  intro x
  have hba : 0 < b - a := sub_pos.mpr hab
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set j := min ⌊(x.1 - a) * m / (b - a)⌋₊ (m - 1)
  have hj_succ : j + 1 ≤ m := by omega
  set t : ℝ := (x.1 - a) * m / (b - a)
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg (sub_nonneg.mpr x.2.1) hm_pos.le) hba.le
  have hlo : sensor a b m j ≤ x.1 := by
    unfold sensor
    have hjt : (j : ℝ) ≤ t := (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht0)
    have h1 : (j : ℝ) * (b - a) / m ≤ t * (b - a) / m := by gcongr
    have h2 : t * (b - a) / m = x.1 - a := by dsimp [t]; field_simp [hba.ne', hm_pos.ne']
    rw [h2] at h1; linarith
  have hhi : x.1 ≤ sensor a b m (j + 1) := by
    by_cases hfl : ⌊t⌋₊ ≤ m - 1
    · have hj_eq : j = ⌊t⌋₊ := min_eq_left hfl
      rw [hj_eq]; unfold sensor
      have ht_lt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h1 : t * (b - a) / m < ((⌊t⌋₊ : ℝ) + 1) * (b - a) / m := by gcongr
      have h2 : t * (b - a) / m = x.1 - a := by dsimp [t]; field_simp [hba.ne', hm_pos.ne']
      rw [h2] at h1; push_cast; linarith
    · have hj_eq : j = m - 1 := by change min ⌊t⌋₊ (m - 1) = m - 1; exact min_eq_right (by omega)
      have hj1 : j + 1 = m := by omega
      rw [hj1, sensor_self'' a b hm]; exact x.2.2
  have hstep_pos : 0 < sensor a b m (j + 1) - sensor a b m j := by
    rw [sensor_succ_sub'' a b hm j]; exact div_pos hba hm_pos
  set lam : ℝ := (x.1 - sensor a b m j) / (sensor a b m (j + 1) - sensor a b m j)
  have hlam0 : 0 ≤ lam := div_nonneg (sub_nonneg.mpr hlo) hstep_pos.le
  have hlam1 : lam ≤ 1 := (div_le_one hstep_pos).mpr (sub_le_sub_right hhi _)
  have heval : ∀ z : Fin (m + 1) → ℝ,
      interpVec hab hm z x =
        z ⟨j, by omega⟩ + (z ⟨j + 1, by omega⟩ - z ⟨j, by omega⟩) /
          (sensor a b m (j + 1) - sensor a b m j) * (x.1 - sensor a b m j) := by
    intro z
    change (if hj : j + 1 ≤ m then
      z ⟨j, by omega⟩ + (z ⟨j + 1, by omega⟩ - z ⟨j, by omega⟩) /
        (sensor a b m (j + 1) - sensor a b m j) * (x.1 - sensor a b m j)
      else 0) = _
    rw [dif_pos hj_succ]
  have hdiff : interpVec hab hm w x - interpVec hab hm v x =
      (1 - lam) * (w ⟨j, by omega⟩ - v ⟨j, by omega⟩) +
        lam * (w ⟨j + 1, by omega⟩ - v ⟨j + 1, by omega⟩) := by
    rw [heval w, heval v]
    dsimp only [lam]
    have hne : sensor a b m (j + 1) - sensor a b m j ≠ 0 := hstep_pos.ne'
    field_simp [hne]
    ring
  have hd_le : ‖w - v‖ < ε := by rwa [← dist_eq_norm]
  have h1 : |w ⟨j, by omega⟩ - v ⟨j, by omega⟩| ≤ ‖w - v‖ :=
    norm_le_pi_norm (w - v) ⟨j, by omega⟩
  have h2 : |w ⟨j + 1, by omega⟩ - v ⟨j + 1, by omega⟩| ≤ ‖w - v‖ :=
    norm_le_pi_norm (w - v) ⟨j + 1, by omega⟩
  change |interpVec hab hm w x - interpVec hab hm v x| < ε
  rw [hdiff]
  calc |(1 - lam) * (w ⟨j, by omega⟩ - v ⟨j, by omega⟩) +
          lam * (w ⟨j + 1, by omega⟩ - v ⟨j + 1, by omega⟩)|
      ≤ |(1 - lam) * (w ⟨j, by omega⟩ - v ⟨j, by omega⟩)| +
          |lam * (w ⟨j + 1, by omega⟩ - v ⟨j + 1, by omega⟩)| := abs_add_le _ _
    _ = (1 - lam) * |w ⟨j, by omega⟩ - v ⟨j, by omega⟩| +
          lam * |w ⟨j + 1, by omega⟩ - v ⟨j + 1, by omega⟩| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlam1), abs_of_nonneg hlam0]
    _ ≤ (1 - lam) * ‖w - v‖ + lam * ‖w - v‖ := by gcongr
    _ = ‖w - v‖ := by ring
    _ < ε := hd_le

-- Integral Gronwall inequality for a continuous nonnegative function on [a, b]
private lemma integral_gronwall {a b c A : ℝ} (hab : a ≤ b) (hc : 0 < c) (hA : 0 ≤ A)
    {φ : ℝ → ℝ} (hφ_cont : Continuous φ)
    (hφ_le : ∀ x ∈ Set.Icc a b, φ x ≤ A + c * ∫ t in a..x, φ t) :
    ∀ x ∈ Set.Icc a b, φ x ≤ A * Real.exp (c * (b - a)) := by
  let I : ℝ → ℝ := fun x => ∫ t in a..x, φ t
  have hI_deriv : ∀ x : ℝ, HasDerivAt I (φ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hφ_cont.intervalIntegrable a x)
      (hφ_cont.stronglyMeasurableAtFilter _ _) hφ_cont.continuousAt
  let H : ℝ → ℝ := fun x =>
    Real.exp (-c * (x - a)) * I x - (A / c) * (1 - Real.exp (-c * (x - a)))
  have hH_deriv : ∀ x : ℝ, HasDerivAt H (Real.exp (-c * (x - a)) * (φ x - c * I x - A)) x := by
    intro x
    have hlin : HasDerivAt (fun y => -c * (y - a)) (-c) x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul (-c)
    have hexp : HasDerivAt (fun y => Real.exp (-c * (y - a))) (Real.exp (-c * (x - a)) * (-c)) x :=
      hlin.exp
    have h1 : HasDerivAt (fun y => Real.exp (-c * (y - a)) * I y)
        (Real.exp (-c * (x - a)) * (-c) * I x + Real.exp (-c * (x - a)) * φ x) x :=
      hexp.mul (hI_deriv x)
    have h2 : HasDerivAt (fun y => (A / c) * (1 - Real.exp (-c * (y - a))))
        ((A / c) * (-(Real.exp (-c * (x - a)) * (-c)))) x :=
      (hexp.const_sub 1).const_mul (A / c)
    have hsub := h1.sub h2
    have hderiv_eq : Real.exp (-c * (x - a)) * (-c) * I x + Real.exp (-c * (x - a)) * φ x -
        (A / c) * (-(Real.exp (-c * (x - a)) * (-c))) =
        Real.exp (-c * (x - a)) * (φ x - c * I x - A) := by
      have hc_cancel : (A / c) * (-(Real.exp (-c * (x - a)) * (-c))) = Real.exp (-c * (x - a)) * A := by
        field_simp [hc.ne']
      rw [hc_cancel]
      ring
    rwa [hderiv_eq] at hsub
  have hH_anti : AntitoneOn H (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun x _ => (hH_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hH_deriv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    have hx_mem : x ∈ Set.Icc a b := interior_subset hx
    rw [(hH_deriv x).deriv]
    have hle := hφ_le x hx_mem
    have hexp_pos : 0 < Real.exp (-c * (x - a)) := Real.exp_pos _
    exact mul_nonpos_of_nonneg_of_nonpos hexp_pos.le (by linarith)
  intro x hx
  have hHa : H a = 0 := by simp [H, I]
  have hHx_le : H x ≤ 0 := by
    rw [← hHa]
    exact hH_anti (Set.left_mem_Icc.mpr hab) hx hx.1
  have hI_bound : c * I x ≤ A * (Real.exp (c * (x - a)) - 1) := by
    dsimp only [H] at hHx_le
    have hmul : Real.exp (c * (x - a)) *
        (Real.exp (-c * (x - a)) * I x - (A / c) * (1 - Real.exp (-c * (x - a)))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hHx_le
    have hexp_inv : Real.exp (c * (x - a)) * Real.exp (-c * (x - a)) = 1 := by
      rw [← Real.exp_add]
      have : c * (x - a) + -c * (x - a) = 0 := by ring
      rw [this, Real.exp_zero]
    have h1 : I x ≤ (A / c) * (Real.exp (c * (x - a)) - 1) := by
      have h2 : Real.exp (c * (x - a)) *
          (Real.exp (-c * (x - a)) * I x - (A / c) * (1 - Real.exp (-c * (x - a)))) =
          I x - (A / c) * (Real.exp (c * (x - a)) - 1) := by
        calc Real.exp (c * (x - a)) *
              (Real.exp (-c * (x - a)) * I x - (A / c) * (1 - Real.exp (-c * (x - a))))
            = (Real.exp (c * (x - a)) * Real.exp (-c * (x - a))) * I x -
                (A / c) * (Real.exp (c * (x - a)) - Real.exp (c * (x - a)) * Real.exp (-c * (x - a))) := by
              ring
          _ = I x - (A / c) * (Real.exp (c * (x - a)) - 1) := by rw [hexp_inv]; ring
      linarith
    have h3 : c * I x ≤ c * ((A / c) * (Real.exp (c * (x - a)) - 1)) :=
      mul_le_mul_of_nonneg_left h1 hc.le
    have h4 : c * ((A / c) * (Real.exp (c * (x - a)) - 1)) = A * (Real.exp (c * (x - a)) - 1) := by
      field_simp [hc.ne']
    linarith
  have hstep1 : φ x ≤ A * Real.exp (c * (x - a)) := by
    have h1 := hφ_le x hx
    linarith
  have hexp_mono : Real.exp (c * (x - a)) ≤ Real.exp (c * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hc.le)
  exact hstep1.trans (mul_le_mul_of_nonneg_left hexp_mono hA)

/-! ### Part 4: Main Theorem (Theorem 2 — number of sensors) -/

theorem solution {a b : ℝ} (hab : a < b) {K : ℕ} (σ : ℝ → ℝ) (hσc : Continuous σ)
    (hσp : ¬ IsPolynomialFun σ) (V : Set C(Set.Icc a b, ℝ)) (hV : IsCompact V)
    (g : (Fin K → ℝ) → ℝ → ℝ → (Fin K → ℝ)) (s₀ : Fin K → ℝ)
    (G : C(Set.Icc a b, ℝ) → C(Set.Icc a b, Fin K → ℝ))
    (hG : SolvesODE a b g s₀ G (sensorHull a b V)) (hGc : ContinuousOn G (sensorHull a b V))
    (c : ℝ) (hc : 0 < c)
    (hL : IsLipschitzSU a b g c (valueSet (G '' sensorHull a b V)) (valueSet (sensorHull a b V)))
    (m : ℕ) (hm : 0 < m) (κ : ℝ)
    (hκ : ∀ u ∈ V, ∀ x ∈ Set.Icc a b, |evalAt u x - interp a b m (evalAt u) x| ≤ κ)
    (ε : ℝ) (hε : c * (b - a) * κ * Real.exp (c * (b - a)) < ε) (d : Set.Icc a b) :
    ∃ (n : ℕ) (W₁ : Matrix (Fin n) (Fin (m + 1)) ℝ) (b₁ : Fin n → ℝ) (W₂ : Matrix (Fin K) (Fin n) ℝ)
      (b₂ : Fin K → ℝ),
      ∀ u ∈ V, eucNorm (G u d - shallowNet σ W₁ b₁ W₂ b₂ (sensorValues a b m u)) < ε := by
  by_cases hVne : V.Nonempty
  · -- κ ≥ 0 because V is nonempty
    obtain ⟨u₀, hu₀⟩ := hVne
    have hκ_nonneg : 0 ≤ κ :=
      (abs_nonneg _).trans (hκ u₀ hu₀ a (Set.left_mem_Icc.mpr hab.le))
    have hA_nonneg : 0 ≤ c * (b - a) * κ := by
      have : 0 < b - a := sub_pos.mpr hab
      positivity
    -- Step 1: Gronwall bound ‖G u d - G (u_m) d‖₂ ≤ c(b-a)κ exp(c(b-a)) for all u ∈ V
    have hgronwall_u : ∀ u ∈ V,
        eucNorm (G u d - G (interpVec hab hm (sensorValues a b m u)) d) ≤
          c * (b - a) * κ * Real.exp (c * (b - a)) := by
      intro u huV
      let um : C(Set.Icc a b, ℝ) := interpVec hab hm (sensorValues a b m u)
      have hum_eq : ∀ x : Set.Icc a b, um x = interp a b m (evalAt u) x.1 := fun x =>
        interpVecFun_sensorValues hm u x.1
      have huW : u ∈ sensorHull a b V :=
        Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨le_rfl, Or.inl huV⟩⟩
      have humW : um ∈ sensorHull a b V :=
        Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, Or.inr ⟨u, huV, hum_eq⟩⟩⟩
      obtain ⟨hint_u, heq_u⟩ := hG u huW
      obtain ⟨hint_um, heq_um⟩ := hG um humW
      let clamp : ℝ → Set.Icc a b := fun t =>
        ⟨max a (min b t), le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
      have hclamp_cont : Continuous clamp :=
        Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id)) _
      have hclamp_eq : ∀ {t : ℝ} (ht : t ∈ Set.Icc a b), clamp t = ⟨t, ht⟩ := by
        intro t ht
        apply Subtype.ext
        dsimp only [clamp]
        rw [min_eq_right ht.2, max_eq_right ht.1]
      let φ : ℝ → ℝ := fun t => eucNorm (G u (clamp t) - G um (clamp t))
      have hφ_cont : Continuous φ :=
        continuous_eucNorm.comp
          (((G u).continuous.comp hclamp_cont).sub ((G um).continuous.comp hclamp_cont))
      have hφ_le : ∀ x ∈ Set.Icc a b, φ x ≤ c * (b - a) * κ + c * ∫ t in a..x, φ t := by
        intro x hx
        let F : ℝ → Fin K → ℝ := fun t =>
          g (evalAt (G u) t) (evalAt u t) t - g (evalAt (G um) t) (evalAt um t) t
        have hint_u_ax : IntervalIntegrable (fun t => g (evalAt (G u) t) (evalAt u t) t) volume a x :=
          hint_u.mono_set (Set.uIcc_subset_uIcc_left (Set.Icc_subset_uIcc hx))
        have hint_um_ax : IntervalIntegrable (fun t => g (evalAt (G um) t) (evalAt um t) t) volume a x :=
          hint_um.mono_set (Set.uIcc_subset_uIcc_left (Set.Icc_subset_uIcc hx))
        have hint_F : IntervalIntegrable F volume a x := hint_u_ax.sub hint_um_ax
        let w : Fin K → ℝ := G u ⟨x, hx⟩ - G um ⟨x, hx⟩
        have hw_eq : w = ∫ t in a..x, F t := by
          dsimp only [w, F]
          rw [heq_u ⟨x, hx⟩, heq_um ⟨x, hx⟩, add_sub_add_left_eq_sub,
            intervalIntegral.integral_sub hint_u_ax hint_um_ax]
        have hF_bd : ∀ t ∈ Set.Icc a x, eucNorm (F t) ≤ c * φ t + c * κ := by
          intro t ht
          have ht_ab : t ∈ Set.Icc a b := ⟨ht.1, ht.2.trans hx.2⟩
          have hs1 : evalAt (G u) t ∈ valueSet (G '' sensorHull a b V) := by
            rw [evalAt, dif_pos ht_ab]
            exact ⟨G u, ⟨u, huW, rfl⟩, ⟨t, ht_ab⟩, rfl⟩
          have hs2 : evalAt (G um) t ∈ valueSet (G '' sensorHull a b V) := by
            rw [evalAt, dif_pos ht_ab]
            exact ⟨G um, ⟨um, humW, rfl⟩, ⟨t, ht_ab⟩, rfl⟩
          have hr1 : evalAt u t ∈ valueSet (sensorHull a b V) := by
            rw [evalAt, dif_pos ht_ab]
            exact ⟨u, huW, ⟨t, ht_ab⟩, rfl⟩
          have hr2 : evalAt um t ∈ valueSet (sensorHull a b V) := by
            rw [evalAt, dif_pos ht_ab]
            exact ⟨um, humW, ⟨t, ht_ab⟩, rfl⟩
          have h1 := hL.1 _ hs1 _ hs2 _ hr1 t ht_ab
          have h2 := hL.2 _ hs2 _ hr1 _ hr2 t ht_ab
          have htri := eucNorm_sub_triangle (g (evalAt (G u) t) (evalAt u t) t)
            (g (evalAt (G um) t) (evalAt u t) t) (g (evalAt (G um) t) (evalAt um t) t)
          have hφt : eucNorm (evalAt (G u) t - evalAt (G um) t) = φ t := by
            dsimp only [φ]
            rw [hclamp_eq ht_ab, evalAt, dif_pos ht_ab, evalAt, dif_pos ht_ab]
          have hκt : |evalAt u t - evalAt um t| ≤ κ := by
            have humev : evalAt um t = interp a b m (evalAt u) t := by
              rw [evalAt, dif_pos ht_ab, hum_eq ⟨t, ht_ab⟩]
            rw [humev]
            exact hκ u huV t ht_ab
          have h2' : c * |evalAt u t - evalAt um t| ≤ c * κ :=
            mul_le_mul_of_nonneg_left hκt hc.le
          rw [hφt] at h1
          dsimp only [F]
          linarith
        -- Cauchy-Schwarz bound on eucNorm w ^ 2 = ∫ t in a..x, ∑ k, w k * F t k
        have hproj_int : ∀ k : Fin K, IntervalIntegrable (fun t => w k * F t k) volume a x := by
          intro k
          let Lk : (Fin K → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) k
          have hp : IntervalIntegrable (fun t => F t k) volume a x :=
            ⟨Lk.integrable_comp hint_F.1, Lk.integrable_comp hint_F.2⟩
          exact hp.const_mul (w k)
        have hdot_int : IntervalIntegrable (fun t => ∑ k : Fin K, w k * F t k) volume a x := by
          have heq : (fun t => ∑ k : Fin K, w k * F t k) = ∑ k : Fin K, fun t => w k * F t k := by
            ext t
            simp [Finset.sum_apply]
          rw [heq]
          exact IntervalIntegrable.sum (Finset.univ : Finset (Fin K))
            (f := fun k t => w k * F t k) (fun k _ => hproj_int k)
        have hw_sq_eq : eucNorm w ^ 2 = ∫ t in a..x, ∑ k : Fin K, w k * F t k := by
          rw [eucNorm_sq]
          have hsum_int : (∫ t in a..x, ∑ k : Fin K, w k * F t k) =
              ∑ k : Fin K, ∫ t in a..x, w k * F t k :=
            intervalIntegral.integral_finsetSum fun k _ => hproj_int k
          rw [hsum_int]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [intervalIntegral.integral_const_mul, sq]
          congr 1
          have hcomm := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => ℝ) k).intervalIntegral_comp_comm hint_F
          simpa [hw_eq] using hcomm.symm
        have hrhs_int : IntervalIntegrable (fun t => eucNorm w * (c * φ t + c * κ)) volume a x :=
          ((hφ_cont.const_mul c).add continuous_const).const_mul (eucNorm w) |>.intervalIntegrable _ _
        have hw_sq_le : eucNorm w ^ 2 ≤ eucNorm w * (c * (x - a) * κ + c * ∫ t in a..x, φ t) := by
          rw [hw_sq_eq]
          have hmono := intervalIntegral.integral_mono_on hx.1 hdot_int hrhs_int fun t ht => by
            calc ∑ k : Fin K, w k * F t k
                ≤ eucNorm w * eucNorm (F t) := dot_le_eucNorm_mul w (F t)
              _ ≤ eucNorm w * (c * φ t + c * κ) :=
                  mul_le_mul_of_nonneg_left (hF_bd t ht) (eucNorm_nonneg w)
          refine hmono.trans_eq ?_
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add ((hφ_cont.const_mul c).intervalIntegrable _ _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
          ring
        have hφx : φ x = eucNorm w := by dsimp only [φ, w]; rw [hclamp_eq hx]
        rw [hφx]
        have hxa_le : c * (x - a) * κ ≤ c * (b - a) * κ := by
          have : x - a ≤ b - a := sub_le_sub_right hx.2 a
          nlinarith
        rcases eq_or_lt_of_le (eucNorm_nonneg w) with hw0 | hwpos
        · rw [← hw0]
          have hint_nonneg : 0 ≤ ∫ t in a..x, φ t :=
            intervalIntegral.integral_nonneg hx.1 fun t _ => eucNorm_nonneg _
          nlinarith
        · have hw_le : eucNorm w ≤ c * (x - a) * κ + c * ∫ t in a..x, φ t := by
            nlinarith
          linarith
      have hres := integral_gronwall hab.le hc hA_nonneg hφ_cont hφ_le d.1 d.2
      dsimp only [φ] at hres
      rwa [hclamp_eq d.2] at hres
    -- Step 2: Universal approximation of Ψ(v) = G (interpVec v) d on S_m = sensorValues '' V
    have hTW : IsTauberWiener σ := continuous_not_poly_isTauberWiener σ hσc hσp
    have hsensor_cont : Continuous (sensorValues a b m) := by
      refine continuous_pi fun j => ?_
      have hj : sensor a b m j.1 ∈ Set.Icc a b := sensor_mem_Icc'' hab hm (Nat.le_of_lt_succ j.2)
      have heq : (fun u : C(Set.Icc a b, ℝ) => sensorValues a b m u j) =
          fun u => u ⟨sensor a b m j.1, hj⟩ := by
        ext u
        rw [sensorValues, evalAt, dif_pos hj]
      rw [heq]
      exact continuous_eval_const (⟨sensor a b m j.1, hj⟩ : Set.Icc a b)
    let Sm : Set (Fin (m + 1) → ℝ) := sensorValues a b m '' V
    have hSm_comp : IsCompact Sm := hV.image hsensor_cont
    let Ψ : (Fin (m + 1) → ℝ) → (Fin K → ℝ) := fun v => G (interpVec hab hm v) d
    have hΨ_cont : ContinuousOn Ψ Sm := by
      have hmaps : Set.MapsTo (interpVec hab hm) Sm (sensorHull a b V) := by
        rintro _ ⟨u, huV, rfl⟩
        exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, Or.inr ⟨u, huV, fun x =>
          interpVecFun_sensorValues hm u x.1⟩⟩⟩
      have hG_comp : ContinuousOn (fun v => G (interpVec hab hm v)) Sm :=
        hGc.comp (interpVec_continuous hab hm).continuousOn hmaps
      exact (continuous_eval_const d).continuousOn.comp hG_comp (Set.mapsTo_univ _ _)
    let δ : ℝ := ε - c * (b - a) * κ * Real.exp (c * (b - a))
    have hδpos : 0 < δ := sub_pos.mpr hε
    have hcoord : ∀ k : Fin K,
        ∃ (nk : ℕ) (ck bk : Fin nk → ℝ) (Wk : Fin nk → Fin (m + 1) → ℝ),
          ∀ v ∈ Sm, |Ψ v k - ∑ i : Fin nk, ck i * σ (∑ j : Fin (m + 1), Wk i j * v j + bk i)| <
            δ / (Real.sqrt K + 1) := by
      intro k
      have hFk : ContinuousOn (fun v => Ψ v k) Sm :=
        (continuous_apply k).continuousOn.comp hΨ_cont (Set.mapsTo_univ _ _)
      exact uat_fin_scalar σ hTW Sm hSm_comp (fun v => Ψ v k) hFk (δ / (Real.sqrt K + 1)) (by positivity)
    choose nk ck bk Wk hnk using hcoord
    -- Stack the K scalar networks block-diagonally into a single shallowNet
    let Idx := Σ k : Fin K, Fin (nk k)
    let n : ℕ := Fintype.card Idx
    let eIdx : Fin n ≃ Idx := (Fintype.equivFin Idx).symm
    let W₁ : Matrix (Fin n) (Fin (m + 1)) ℝ := fun r j => Wk (eIdx r).1 (eIdx r).2 j
    let b₁ : Fin n → ℝ := fun r => bk (eIdx r).1 (eIdx r).2
    let W₂ : Matrix (Fin K) (Fin n) ℝ := fun k r =>
      if h : (eIdx r).1 = k then ck k (h ▸ (eIdx r).2) else 0
    let b₂ : Fin K → ℝ := 0
    refine ⟨n, W₁, b₁, W₂, b₂, fun u huV => ?_⟩
    have hvSm : sensorValues a b m u ∈ Sm := ⟨u, huV, rfl⟩
    have hnet_coord : ∀ k : Fin K,
        shallowNet σ W₁ b₁ W₂ b₂ (sensorValues a b m u) k =
          ∑ i : Fin (nk k), ck k i * σ (∑ j : Fin (m + 1), Wk k i j * sensorValues a b m u j + bk k i) := by
      intro k
      simp only [shallowNet, b₂, add_zero, Matrix.mulVec, dotProduct, W₂, W₁, b₁]
      have hreidx : (∑ r : Fin n,
          (if h : (eIdx r).1 = k then ck k (h ▸ (eIdx r).2) else 0) *
            σ (∑ j : Fin (m + 1), Wk (eIdx r).1 (eIdx r).2 j * sensorValues a b m u j +
              bk (eIdx r).1 (eIdx r).2)) =
          ∑ p : Idx, (if h : p.1 = k then ck k (h ▸ p.2) else 0) *
            σ (∑ j : Fin (m + 1), Wk p.1 p.2 j * sensorValues a b m u j + bk p.1 p.2) :=
        Equiv.sum_comp eIdx (fun p : Idx =>
          (if h : p.1 = k then ck k (h ▸ p.2) else 0) *
            σ (∑ j : Fin (m + 1), Wk p.1 p.2 j * sensorValues a b m u j + bk p.1 p.2))
      rw [hreidx, Fintype.sum_sigma, Finset.sum_eq_single k]
      · refine Finset.sum_congr rfl fun i _ => by simp
      · intro k' _ hk'
        exact Finset.sum_eq_zero fun i _ => by simp [hk']
      · intro h; exact (h (Finset.mem_univ k)).elim
    have hnet_err : eucNorm (Ψ (sensorValues a b m u) -
        shallowNet σ W₁ b₁ W₂ b₂ (sensorValues a b m u)) < δ := by
      unfold eucNorm
      have hsq_lt : (∑ k : Fin K, (Ψ (sensorValues a b m u) k -
          shallowNet σ W₁ b₁ W₂ b₂ (sensorValues a b m u) k) ^ 2) < δ ^ 2 := by
        calc ∑ k : Fin K, (Ψ (sensorValues a b m u) k -
                shallowNet σ W₁ b₁ W₂ b₂ (sensorValues a b m u) k) ^ 2
            ≤ ∑ _k : Fin K, (δ / (Real.sqrt K + 1)) ^ 2 := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [hnet_coord k]
              have hlt := hnk k (sensorValues a b m u) hvSm
              rw [← sq_abs]
              exact sq_le_sq' (by linarith [abs_nonneg (Ψ (sensorValues a b m u) k -
                ∑ i : Fin (nk k), ck k i * σ (∑ j, Wk k i j * sensorValues a b m u j + bk k i))]) hlt.le
          _ = (K : ℝ) * (δ / (Real.sqrt K + 1)) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ < δ ^ 2 := by
              have hden : 0 < Real.sqrt K + 1 := by positivity
              have hK_lt : (K : ℝ) < (Real.sqrt K + 1) ^ 2 := by
                have hsqK : Real.sqrt K ^ 2 = (K : ℝ) := Real.sq_sqrt (Nat.cast_nonneg K)
                have hsqrt_nn : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
                nlinarith
              rw [div_pow, mul_div_assoc', div_lt_iff₀ (sq_pos_of_pos hden)]
              have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδpos
              nlinarith
      exact (Real.sqrt_lt' hδpos).mpr hsq_lt
    have htri := eucNorm_sub_triangle (G u d) (Ψ (sensorValues a b m u))
      (shallowNet σ W₁ b₁ W₂ b₂ (sensorValues a b m u))
    have hgron := hgronwall_u u huV
    dsimp only [Ψ] at htri hnet_err
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hVne
    refine ⟨0, 0, 0, 0, 0, fun u huV => ?_⟩
    rw [hVne] at huV
    exact huV.elim
