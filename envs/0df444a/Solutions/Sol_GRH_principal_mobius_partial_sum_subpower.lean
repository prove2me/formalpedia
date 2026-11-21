-- Prove2me | solution 1 for GRH.principal_mobius_partial_sum_subpower
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:30:38.263825+00:00
-- url     : https://prove2.me/submissions/c2daddc6-81d7-4650-9181-8048c3093078

import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_logarithmic_control
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_same_height_mem_disk
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_le_of_re_pos
import Theorems.Thm_GRH_dirichlet_small_disk_log_uniform
import Theorems.Thm_Titchmarsh_partialSum_isBigO_of_holomorphic_growth
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
open Filter Complex Metric Set
open scoped Topology ComplexConjugate

private theorem GRH.differentiableOn_principal_inv_with_pole_removed (q : ℕ) [NeZero q]
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    (hzeta : ∀ s : ℂ, a < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ (Function.update (fun s ↦ (DirichletCharacter.LFunctionTrivChar q s)⁻¹) 1 0)
      {s : ℂ | a < s.re} := by
  have ha : {s : ℂ | a < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using ha₁)
  apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff ha).1
  constructor
  · intro s hs
    obtain ⟨hsr, hne⟩ := hs
    change s ≠ 1 at hne
    have hL : DirichletCharacter.LFunctionTrivChar q s ≠ 0 := by
      rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_) (hzeta s hsr hne)
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
      have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos (ha₀.trans_lt hsr))
      intro h
      rw [← sub_eq_zero.mp h, norm_one] at hnorm
      exact lt_irrefl _ hnorm
    apply DifferentiableAt.differentiableWithinAt
    apply (((1 : DirichletCharacter ℂ q).differentiableAt_LFunction s (.inl hne)).inv hL).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hne] with z hz
    exact Function.update_of_ne hz ..
  · apply continuousAt_update_same.mpr
    let R : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹)
    have hR : R ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p hp h ↦ ?_
      have hp1 : (p : ℂ) ≠ 1 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_one
      exact hp1 (by simpa using congrArg Inv.inv (sub_eq_zero.mp h).symm)
    have hnum : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 1) (𝓝 0) := by
      simpa using (tendsto_id.sub_const (1 : ℂ)).mono_left (nhdsWithin_le_nhds (a := (1 : ℂ)) (s := {1}ᶜ))
    have hquot := hnum.div (DirichletCharacter.LFunctionTrivChar_residue_one (N := q)) hR
    simp only [zero_div] at hquot
    apply hquot.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    simp [div_eq_mul_inv, hne, mul_comm]

private theorem GRH.principal_inv_norm_le_eulerFactor_mul_zeta_inv (q : ℕ) [NeZero q]
    {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : a ≤ s.re) (hs₁ : s ≠ 1) :
    ‖(DirichletCharacter.LFunctionTrivChar q s)⁻¹‖ ≤
      (∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-a))⁻¹) * ‖(riemannZeta s)⁻¹‖ := by
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs₁, mul_inv, norm_mul,
    ← Finset.prod_inv_distrib, Complex.norm_prod]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  have hpos : 0 < 1 - (p : ℝ) ^ (-a) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos ha))
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-a) := by
    rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (neg_le_neg hs)
  have hfactor : 1 - (p : ℝ) ^ (-a) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    calc 1 - (p : ℝ) ^ (-a) ≤ ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-s)‖ := by rw [norm_one]; exact sub_le_sub_left hpow 1
         _ ≤ _ := norm_sub_norm_le _ _
  rw [norm_inv]
  exact (inv_le_inv₀ (hpos.trans_le hfactor) hpos).2 hfactor

private theorem zeta_ne_above_threshold {s : ℂ} (hs : 0.8749570698 < s.re) (hs₁ : s ≠ 1) : riemannZeta s ≠ 0 := by
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound (1 : DirichletCharacter ℂ 1) hs (by simpa using hs₁)

open OAI.SevenEighths.LogarithmicControl in
private theorem zeta_inv_high_strip (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, 0.8749570698 + δ ≤ s.re → s.re ≤ 2 → 4 ≤ |s.im| →
      ‖(riemannZeta s)⁻¹‖ ≤ D * (8 + |s.im|) ^ ε := by
  let e : ℝ := min (δ / 8) (1 / 2000)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he' : e < 1 / 1000 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδe : 8 * e ≤ δ := by have := min_le_left (δ / 8) (1 / 2000); dsimp [e]; linarith
  obtain ⟨A, hA, hsmall⟩ := GRH.dirichlet_small_disk_log_uniform
  obtain ⟨D, hDpos, hD⟩ := logarithmic_control (e := e) (A := A)
    (M := 2) (ε := ε) he he' hA (by norm_num) hε
  refine ⟨D, hDpos, ?_⟩
  intro s hs₀ hs₂ him
  let c : ℂ := 2 + (s.im : ℂ) * I
  have hc : c.re = 2 := by simp [c]
  have hci : c.im = s.im := by simp [c]
  have hgeo {z : ℂ} (hz : z ∈ ball c (2 - 0.8749570698 - 2 * e)) :
      0.8749570698 < z.re ∧ 1 ≤ |z.im| ∧ ‖z‖ ≤ 4 + |s.im| := by
    have hre := Complex.abs_re_le_norm (z - c)
    have him' := Complex.abs_im_le_norm (z - c)
    rw [sub_re, hc] at hre
    rw [sub_im, hci] at him'
    rw [mem_ball, dist_eq_norm] at hz
    have hdist : ‖z - c‖ < 2 := by linarith
    have habs := abs_sub_abs_le_abs_sub s.im z.im
    rw [abs_sub_comm] at habs
    have hcz : ‖c‖ ≤ 2 + |s.im| := by simpa [hc, hci] using Complex.norm_le_abs_re_add_abs_im c
    refine ⟨by linarith [(abs_lt.mp (hre.trans_lt hz)).1], by linarith, ?_⟩
    have ht := norm_add_le (z - c) c
    rw [sub_add_cancel] at ht
    linarith
  have h1 {z : ℂ} (hz : z ∈ ball c (2 - 0.8749570698 - 2 * e)) : z ≠ 1 := by
    intro h
    have := (hgeo hz).2.1
    norm_num [h] at this
  obtain ⟨E, hE, hExp, hEb⟩ := hsmall 1 (1 : DirichletCharacter ℂ 1) c hc
  rw [DirichletCharacter.LFunction_modOne_eq] at hExp
  have hpoly (z : ℂ) (hz : z ∈ ball c (2 - 0.8749570698 - 3 * e)) :
      ‖riemannZeta z‖ ≤ (8 + |s.im|) ^ (2 : ℝ) := by
    have hb : z ∈ ball c (2 - 0.8749570698 - 2 * e) := ball_subset_ball (by linarith) hz
    obtain ⟨hr, hi, hn⟩ := hgeo hb
    have hp : 0 < z.re := by linarith
    have hden : 1 ≤ ‖1 - z‖ := by
      simpa using hi.trans (by simpa using Complex.abs_im_le_norm (1 - z))
    have hdiv : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
      apply (div_le_iff₀ hp).2
      nlinarith [mul_nonneg (norm_nonneg z) (show 0 ≤ z.re - 1 / 2 by linarith)]
    have hsmall : 1 / ‖1 - z‖ ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden).trans_eq (by norm_num)
    have hbnd := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hp (h1 hb)
    rw [Real.rpow_two]
    nlinarith [sq_nonneg |s.im|, abs_nonneg s.im]
  have hC : Real.exp 1 ≤ 8 + |s.im| := by linarith [Real.exp_one_lt_d9, abs_nonneg s.im]
  obtain ⟨hbound, _⟩ := hD (0.8749570698) (8 + |s.im|) riemannZeta E c (by norm_num) (by norm_num) hC
    (fun z hz ↦ (differentiableAt_riemannZeta (h1 hz)).differentiableWithinAt)
    (fun z hz ↦ zeta_ne_above_threshold (hgeo hz).1 (h1 hz)) hpoly hE hExp hEb
  have hm := same_height_mem_disk (a := 0.8749570698) (e := e) (v := δ)
    (t := s.im) hδe hs₀ hs₂
  rw [Complex.re_add_im] at hm
  exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hbound s (closedBall_subset_closedBall (by linarith) hm))

private theorem principal_strip_growth (q : ℕ) [NeZero q] (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ s : ℂ, 0.8749570698 + δ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖(DirichletCharacter.LFunctionTrivChar q s)⁻¹‖ ≤ C * |s.im| ^ ε := by
  let F : ℂ → ℂ := Function.update (fun s ↦ (DirichletCharacter.LFunctionTrivChar q s)⁻¹) 1 0
  have hhol : DifferentiableOn ℂ F {s : ℂ | 0.8749570698 < s.re} :=
    GRH.differentiableOn_principal_inv_with_pole_removed q (by norm_num) (by norm_num)
      (fun _ hs _ ↦ zeta_ne_above_threshold hs (by assumption))
  let K : Set ℂ := Icc (0.8749570698 + δ) 2 ×ℂ Icc (-4 : ℝ) 4
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hhol.continuousOn.mono (show K ⊆ _ from by
    intro z hz
    have h : 0.8749570698 + δ ≤ z.re := hz.1.1
    change 0.8749570698 < z.re
    linarith))
  obtain ⟨D, hD, hlarge⟩ := zeta_inv_high_strip δ ε hδ hε
  let P := ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(0.8749570698 : ℝ)))⁻¹
  have hP : 0 ≤ P := Finset.prod_nonneg fun p hp ↦ inv_nonneg.mpr (sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)
      (by norm_num)).le)
  refine ⟨max (max 0 B) (P * D * 9 ^ ε), ?_⟩
  intro s hσ h₂ him
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at him
  have him0 : 0 ≤ |s.im| := abs_nonneg _
  have hpw : 1 ≤ |s.im| ^ ε := Real.one_le_rpow him hε.le
  by_cases h4 : 4 ≤ |s.im|
  · have hbound := GRH.principal_inv_norm_le_eulerFactor_mul_zeta_inv q
        (a := 0.8749570698) (by norm_num) (by linarith : 0.8749570698 ≤ s.re) hs1
    change _ ≤ P * _ at hbound
    have hpow : (8 + |s.im|) ^ ε ≤ 9 ^ ε * |s.im| ^ ε := by
      rw [← Real.mul_rpow (by norm_num) him0]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
    calc _ ≤ P * (D * (8 + |s.im|) ^ ε) := hbound.trans <| mul_le_mul_of_nonneg_left (hlarge s hσ h₂ h4) hP
         _ ≤ P * (D * (9 ^ ε * |s.im| ^ ε)) := by gcongr
         _ = (P * D * 9 ^ ε) * |s.im| ^ ε := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hlow : ‖F s‖ ≤ B := hB s ⟨⟨hσ, h₂⟩, abs_le.mp (by linarith : |s.im| ≤ 4)⟩
    rw [show F s = _ from Function.update_of_ne hs1 ..] at hlow
    calc _ ≤ max 0 B := hlow.trans (le_max_right _ _)
         _ ≤ max 0 B * |s.im| ^ ε := le_mul_of_one_le_right (le_max_left _ _) hpw
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

open Filter Asymptotics

theorem solution (q : ℕ) [NeZero q] (σ : ℝ) (hσ : (0.8749570698 : ℝ) < σ) :
    (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1),
      (1 : DirichletCharacter ℂ q) k * (ArithmeticFunction.moebius k : ℂ))
      =O[atTop] (fun N : ℕ ↦ (N : ℝ) ^ σ) := by
  let χ := (1 : DirichletCharacter ℂ q)
  let a (k : ℕ) : ℂ := χ k * (ArithmeticFunction.moebius k : ℂ)
  let F := Function.update (fun s ↦ (DirichletCharacter.LFunctionTrivChar q s)⁻¹) 1 0
  have hF : DifferentiableOn ℂ F {s : ℂ | 0.8749570698 < s.re} :=
    GRH.differentiableOn_principal_inv_with_pole_removed q (by norm_num) (by norm_num)
      (fun _ h h₁ ↦ zeta_ne_above_threshold h h₁)
  have hL (s : ℂ) (h : 1 < s.re) : F s = LSeries a s := by
    have h₁ : s ≠ 1 := by rintro rfl; simp at h
    dsimp only [F]
    rw [Function.update_of_ne h₁]
    change (χ.LFunction s)⁻¹ = _
    rw [χ.LFunction_eq_LSeries h]
    exact inv_eq_of_mul_eq_one_right (DirichletCharacter.LSeries.mul_mu_eq_one χ h)
  have hg (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) := principal_strip_growth q δ ε hδ hε
  have ha (k : ℕ) : ‖a k‖ ≤ 1 := by
    have hμ : ‖(ArithmeticFunction.moebius k : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
    change ‖χ k * _‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (χ.norm_le_one k) (norm_nonneg _)).trans (by simpa using hμ)
  have hperron := Titchmarsh.partialSum_isBigO_of_holomorphic_growth a ha _ (by norm_num) F hF hL
    (fun δ hδ ε hε ↦ by
      obtain ⟨C, hC⟩ := hg δ hδ ε hε
      refine ⟨C, fun s hs h₂ h₃ ↦ ?_⟩
      have hs₁ : s ≠ 1 := by rintro rfl; norm_num at h₃
      simpa only [F, Function.update_of_ne hs₁] using hC s hs h₂ h₃)
    (σ - 0.8749570698) (by linarith)
  have hsum (N : ℕ) : ∑ k ∈ Finset.range (N + 1), a k = ∑ k ∈ Finset.Icc 1 N, a k := by
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp [a]
  change (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), a k) =O[atTop] _
  simp_rw [hsum]
  simpa only [show (0.8749570698 : ℝ) + (σ - 0.8749570698) = σ by ring] using hperron
