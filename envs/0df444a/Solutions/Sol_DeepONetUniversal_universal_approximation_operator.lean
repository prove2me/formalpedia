-- Prove2me | solution 1 for DeepONetUniversal.universal_approximation_operator
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T23:39:53.351623+00:00
-- url     : https://prove2.me/submissions/a400d467-fc30-4bc6-adec-b21aa4fd7a0c

import Mathlib
import Definitions.Def_DeepONetUniversal_Basic
import Theorems.Thm_DeepONetUniversal_universal_approximation_operator_tw

open MeasureTheory Filter Topology DeepONetUniversal
open scoped Convolution ContDiff

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

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {d : ℕ} (σ : ℝ → ℝ) (hσc : Continuous σ) (hσp : ¬ IsPolynomialFun σ)
    (K₁ : Set X) (hK₁ : IsCompact K₁) (hK₁ne : K₁.Nonempty)
    (K₂ : Set (Fin d → ℝ)) (hK₂ : IsCompact K₂)
    (V : Set C(K₁, ℝ)) (hV : IsCompact V) (G : C(K₁, ℝ) → C(K₂, ℝ)) (hG : ContinuousOn G V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n p m : ℕ, 0 < n ∧ 0 < p ∧ 0 < m ∧
      ∃ (c : Fin p → Fin n → ℝ) (ξ : Fin p → Fin n → Fin m → ℝ) (θ : Fin p → Fin n → ℝ)
        (ζ : Fin p → ℝ) (w : Fin p → Fin d → ℝ) (x : Fin m → K₁),
        ∀ u ∈ V, ∀ y : K₂, |G u y - operatorNet σ c ξ θ w ζ (fun j => u (x j)) y| < ε :=
  universal_approximation_operator_tw σ (continuous_not_poly_isTauberWiener σ hσc hσp)
    K₁ hK₁ hK₁ne K₂ hK₂ V hV G hG ε hε
