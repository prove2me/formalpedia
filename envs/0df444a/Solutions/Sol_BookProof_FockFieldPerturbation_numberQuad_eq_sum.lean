-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.numberQuad_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:19:20.612279+00:00
-- url     : https://prove2.me/submissions/c30abd62-5361-440a-86a3-e03028522a98

import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_right
import Theorems.Thm_BookProof_FockSecondQuantization_inner_creA_right
import Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_nonneg
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
import Theorems.Thm_BookProof_FockNumberPreservingGap_numberCol_eq
import Theorems.Thm_BookProof_FockNumberPreservingGap_dGamma_shiftCol
import Theorems.Thm_BookProof_FockNumberPreservingGap_number_quadForm_ge
-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.numberQuad_eq_sum
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_toLp_add (x y : FockAlg) : toLp (x + y) = toLp x + toLp y := map_add toLpL x y

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_toLp_sub (x y : FockAlg) : toLp (x - y) = toLp x - toLp y := map_sub toLpL x y

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_toLp_smul (c : ℂ) (x : FockAlg) : toLp (c • x) = c • toLp x := map_smul toLpL c x

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_toLp_sum {ι : Type*} (s : Finset ι) (g : ι → FockAlg) :
    toLp (∑ j ∈ s, g j) = ∑ j ∈ s, toLp (g j) := map_sum toLpL g s

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_annVec_apply (f : ℕ →₀ ℂ) (x : FockAlg) :
    annVec f x = ∑ j ∈ f.support, ((starRingEnd ℂ) (f j)) • annA j x := by
  simp [annVec, LinearMap.sum_apply]

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_numberQuad_eq_sum {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    numberQuad u = ∑ k ∈ K, ‖toLp (annA k u)‖ ^ 2 := by
  unfold numberQuad
  have hL : ∀ k ∈ modes u ∪ modes u, (numberCol k).support ⊆ K := by
    intro k hk j hj
    rw [numberCol_eq, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hj
    subst hj
    rw [Finset.union_self] at hk
    exact hK hk
  rw [inner_dGamma_right numberCol u u hK hL]
  have e : ∀ j ∈ K, ∑ k ∈ K, (numberCol j) k * (inner ℂ (toLp (annA k u)) (toLp (annA j u)) : ℂ)
      = inner ℂ (toLp (annA j u)) (toLp (annA j u)) := by
    intro j hj
    simp only [numberCol_eq, Finsupp.single_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]; simp [hj]
  rw [Finset.sum_congr rfl e, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := inner_self_eq_norm_sq (𝕜 := ℂ) (toLp (annA j u))
  simpa using this

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_sum_sq_le (u : FockAlg) (S : Finset ℕ) :
    ∑ k ∈ S, ‖toLp (annA k u)‖ ^ 2 ≤ numberQuad u := by
  rw [hbp_numberQuad_eq_sum (K := S ∪ modes u) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => by positivity)

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_numberQuad_nonneg (u : FockAlg) : 0 ≤ numberQuad u := by
  rw [hbp_numberQuad_eq_sum (subset_refl _)]
  exact Finset.sum_nonneg fun _ _ => by positivity

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_inner_creVec_annVec (f : ℕ →₀ ℂ) (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp (creVec f v)) : ℂ) = inner ℂ (toLp (annVec f u)) (toLp v) := by
  rw [creVec_apply, hbp_annVec_apply, hbp_toLp_sum, hbp_toLp_sum, inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hbp_toLp_smul, hbp_toLp_smul, inner_smul_right, inner_smul_left, inner_creA_right]
  simp

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_l2norm_nonneg (f : ℕ →₀ ℂ) : 0 ≤ l2norm f := Real.sqrt_nonneg _

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_norm_annVec_le (f : ℕ →₀ ℂ) (u : FockAlg) :
    ‖toLp (annVec f u)‖ ≤ l2norm f * Real.sqrt (numberQuad u) := by
  rw [hbp_annVec_apply, hbp_toLp_sum]
  calc ‖∑ j ∈ f.support, toLp ((starRingEnd ℂ) (f j) • annA j u)‖
      ≤ ∑ j ∈ f.support, ‖toLp ((starRingEnd ℂ) (f j) • annA j u)‖ := norm_sum_le _ _
    _ = ∑ j ∈ f.support, ‖f j‖ * ‖toLp (annA j u)‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hbp_toLp_smul, norm_smul, Complex.norm_conj]
    _ ≤ Real.sqrt (∑ j ∈ f.support, ‖f j‖ ^ 2) * Real.sqrt (∑ j ∈ f.support, ‖toLp (annA j u)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ l2norm f * Real.sqrt (numberQuad u) := by
        unfold l2norm
        gcongr
        exact hbp_sum_sq_le u _

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_abs_re_inner_fieldVec_le (f : ℕ →₀ ℂ) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re|
      ≤ 2 * l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by
  have e : fieldVec f u = creVec f u + annVec f u := rfl
  rw [e, hbp_toLp_add, inner_add_right, hbp_inner_creVec_annVec, Complex.add_re]
  have h1 : |(inner ℂ (toLp (annVec f u)) (toLp u) : ℂ).re| ≤ ‖toLp (annVec f u)‖ * ‖toLp u‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : |(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re| ≤ ‖toLp u‖ * ‖toLp (annVec f u)‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h3 := hbp_norm_annVec_le f u
  have h4 := norm_nonneg (toLp u)
  calc _ ≤ |(inner ℂ (toLp (annVec f u)) (toLp u) : ℂ).re|
        + |(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re| := abs_add_le _ _
    _ ≤ 2 * ‖toLp (annVec f u)‖ * ‖toLp u‖ := by linarith
    _ ≤ 2 * (l2norm f * Real.sqrt (numberQuad u)) * ‖toLp u‖ := by gcongr
    _ = _ := by ring

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_number_le_dGamma {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ}
    (hgap : IsPosCol (shiftCol col mu)) (u : FockAlg) :
    mu * numberQuad u ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
  have h := inner_dGamma_nonneg hgap u
  rw [dGamma_shiftCol, hbp_toLp_sub, inner_sub_right, hbp_toLp_smul, inner_smul_right,
    Complex.sub_re, Complex.re_ofReal_mul] at h
  unfold numberQuad
  linarith

theorem hbp_two_mul_sqrt_le {c n N t : ℝ} (hN : 0 ≤ N) (ht : 0 < t) :
    2 * c * Real.sqrt N * n ≤ t * N + c ^ 2 / t * n ^ 2 := by
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have key : 0 ≤ t * (t * N + c ^ 2 / t * n ^ 2 - 2 * c * Real.sqrt N * n) := by
    have : t * (t * N + c ^ 2 / t * n ^ 2 - 2 * c * Real.sqrt N * n)
        = (t * Real.sqrt N - c * n) ^ 2 := by
      field_simp
      nth_rewrite 1 [← hs]; ring
    rw [this]; positivity
  have := (mul_nonneg_iff_of_pos_left ht).mp key
  linarith

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_relative {col : ℕ → (ℕ →₀ ℂ)} {mu t : ℝ} (hmu : 0 < mu)
    (ht : 0 < t) (hgap : IsPosCol (shiftCol col mu)) (f : ℕ →₀ ℂ) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re|
      ≤ t / mu * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + l2norm f ^ 2 / t * ‖toLp u‖ ^ 2 := by
  have h1 := hbp_abs_re_inner_fieldVec_le f u
  have h2 := hbp_two_mul_sqrt_le (c := l2norm f) (n := ‖toLp u‖) (hbp_numberQuad_nonneg u) ht
  have h3 := hbp_number_le_dGamma hgap u
  have h4 : t * numberQuad u ≤ t / mu * (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hmu]
    nlinarith
  linarith

open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
  BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation in
theorem hbp_fock_gap {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu)
    (hgap : IsPosCol (shiftCol col mu)) {f : ℕ →₀ ℂ} (hf : l2norm f ≤ mu)
    {u : FockAlg} (h0 : u 0 = 0) :
    (mu - 2 * l2norm f) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re := by
  set q := (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
  set v := (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re
  set l := l2norm f
  have hl : 0 ≤ l := hbp_l2norm_nonneg f
  have hN := number_quadForm_ge h0
  have hq : mu * ‖toLp u‖ ^ 2 ≤ q := by
    have := hbp_number_le_dGamma hgap u
    unfold numberQuad at this
    nlinarith
  rcases hl.eq_or_lt with hl0 | hlpos
  · have : |v| ≤ 2 * l * Real.sqrt (numberQuad u) * ‖toLp u‖ := hbp_abs_re_inner_fieldVec_le f u
    rw [← hl0] at this
    simp only [mul_zero, zero_mul] at this
    have hv : v = 0 := abs_nonpos_iff.mp this
    rw [hv, ← hl0]; linarith
  · have hr := hbp_relative hmu hlpos hgap f u
    have hv := neg_abs_le v
    have e : l ^ 2 / l = l := by field_simp
    rw [e] at hr
    have hlm : 0 ≤ 1 - l / mu := by
      rw [sub_nonneg, div_le_one hmu]; exact hf
    have : (1 - l / mu) * (mu * ‖toLp u‖ ^ 2) ≤ (1 - l / mu) * q := mul_le_mul_of_nonneg_left hq hlm
    have e2 : (1 - l / mu) * (mu * ‖toLp u‖ ^ 2) = (mu - l) * ‖toLp u‖ ^ 2 := by
      field_simp
    have e3 : (1 - l / mu) * q = q - l / mu * q := by ring
    nlinarith

theorem solution {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    numberQuad u = ∑ k ∈ K, ‖toLp (annA k u)‖ ^ 2 := by
  exact hbp_numberQuad_eq_sum hK

