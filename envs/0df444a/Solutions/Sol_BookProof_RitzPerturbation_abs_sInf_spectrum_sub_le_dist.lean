-- Prove2me | solution 1 for BookProof.RitzPerturbation.abs_sInf_spectrum_sub_le_dist
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:06:20.289401+00:00
-- url     : https://prove2.me/submissions/4ceb2f43-cd75-4812-a765-8eb39e69a0c7

import Definitions.Def_ChapterSirkRitzPerturbation
-- Adapted prerequisite proofs: Copyright 2026 Leonardo Pedro, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkRitzSpectrum.lean
noncomputable section
open BookProof.RitzMinMax BookProof.RitzPerturbation BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
set_option autoImplicit false
set_option linter.unusedSectionVars false
private theorem ritzR_abs (T : F →L[ℂ] F) (x : F) :
    |rayleighVal T x| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc
    |rayleighVal T x| ≤ ‖x‖ * ‖T x‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm x (T x))
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

private theorem ritzR_unit (T : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    |rayleighVal T x| ≤ ‖T‖ := by
  simpa only [hx, one_pow, mul_one] using ritzR_abs T x

private theorem ritzR_bddAbove (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    BddAbove (rayleighSetOn T S) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨x, hxS, hx, rfl⟩
  exact (abs_le.mp (ritzR_unit T hx)).2

private theorem ritzR_sup_le (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    rayleighSup T S ≤ ‖T‖ := by
  by_cases hne : (rayleighSetOn T S).Nonempty
  · apply csSup_le hne
    rintro r ⟨x, hxS, hx, rfl⟩
    exact (abs_le.mp (ritzR_unit T hx)).2
  · have he := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [rayleighSup, he, Real.sSup_empty] using norm_nonneg T

private theorem ritzR_le_sup (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    -‖T‖ ≤ rayleighSup T S := by
  by_cases hne : (rayleighSetOn T S).Nonempty
  · obtain ⟨r, hr⟩ := hne
    obtain ⟨x, hxS, hx, rfl⟩ := hr
    exact (abs_le.mp (ritzR_unit T hx)).1.trans
      (le_csSup (ritzR_bddAbove T S) ⟨x, hxS, hx, rfl⟩)
  · have he := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [rayleighSup, he, Real.sSup_empty] using neg_nonpos.mpr (norm_nonneg T)

private theorem ritzR_bddBelow (T : F →L[ℂ] F) (k : ℕ) :
    BddBelow (minmaxSet T k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨S, hd, rfl⟩
  exact ritzR_le_sup T S

private theorem ritzP_ne (T : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : (rayleighSetOn T S).Nonempty := by
  letI : Nontrivial S := Module.nontrivial_of_finrank_pos hS
  obtain ⟨x, hx⟩ := exists_norm_eq (E := S) (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨rayleighVal T (x : F), (x : F), x.property, hx, rfl⟩

private theorem ritzP_ne_congr (T T' : F →L[ℂ] F) {k : ℕ}
    (h : (minmaxSet T k).Nonempty) : (minmaxSet T' k).Nonempty := by
  obtain ⟨r, S, hd, hr⟩ := h
  exact ⟨rayleighSup T' S, S, hd, rfl⟩

private theorem ritzP_neIn_congr (T T' : F →L[ℂ] F) {W : Submodule ℂ F} {k : ℕ}
    (h : (minmaxSetIn T W k).Nonempty) : (minmaxSetIn T' W k).Nonempty := by
  obtain ⟨r, S, hSW, hd, hr⟩ := h
  exact ⟨rayleighSup T' S, S, hSW, hd, rfl⟩

private theorem ritzP_val (T T' : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    |rayleighVal T x - rayleighVal T' x| ≤ ‖T - T'‖ := by
  simpa only [rayleighVal, ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    using ritzR_unit (T - T') hx

private theorem ritzP_sup (T T' : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : rayleighSup T S ≤ rayleighSup T' S + ‖T - T'‖ := by
  apply csSup_le (ritzP_ne T hS)
  rintro r ⟨x, hxS, hx, rfl⟩
  have hm : rayleighVal T' x ≤ rayleighSup T' S :=
    le_csSup (ritzR_bddAbove T' S) ⟨x, hxS, hx, rfl⟩
  have hb := (abs_le.mp (ritzP_val T T' hx)).2
  linarith

private theorem ritzP_bddIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    BddBelow (minmaxSetIn T W k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨S, hSW, hd, rfl⟩
  exact ritzR_le_sup T S

private theorem ritzP_level (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T' k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevel T' k + ‖T - T'‖ := by
  have hh : minmaxLevel T k - ‖T - T'‖ ≤ minmaxLevel T' k := by
    apply le_csInf hne
    rintro r ⟨S, hd, rfl⟩
    have ha : minmaxLevel T k ≤ rayleighSup T S :=
      csInf_le (ritzR_bddBelow T k) ⟨S, hd, rfl⟩
    have hb := ritzP_sup T T' (show 0 < Module.finrank ℂ S by omega)
    linarith
  linarith

private theorem ritzP_levelIn (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T' W k).Nonempty) :
    minmaxLevelIn T W k ≤ minmaxLevelIn T' W k + ‖T - T'‖ := by
  have hh : minmaxLevelIn T W k - ‖T - T'‖ ≤ minmaxLevelIn T' W k := by
    apply le_csInf hne
    rintro r ⟨S, hSW, hd, rfl⟩
    have ha : minmaxLevelIn T W k ≤ rayleighSup T S :=
      csInf_le (ritzP_bddIn T W k) ⟨S, hSW, hd, rfl⟩
    have hb := ritzP_sup T T' (show 0 < Module.finrank ℂ S by omega)
    linarith
  linarith

private theorem ritzP_absLevel (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T k).Nonempty) :
    |minmaxLevel T k - minmaxLevel T' k| ≤ ‖T - T'‖ := by
  have ha := ritzP_level T T' k (ritzP_ne_congr T T' hne)
  have hb := ritzP_level T' T k hne
  rw [norm_sub_rev] at hb
  apply abs_le.mpr
  constructor <;> linarith

private theorem ritzP_absGap (T T' : F →L[ℂ] F)
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    |minmaxGap T - minmaxGap T'| ≤ 2 * ‖T - T'‖ := by
  obtain ⟨ha0, hb0⟩ := abs_le.mp (ritzP_absLevel T T' 0 hne0)
  obtain ⟨ha1, hb1⟩ := abs_le.mp (ritzP_absLevel T T' 1 hne1)
  unfold minmaxGap
  apply abs_le.mpr
  constructor <;> linarith

private theorem ritzG_smul (T : F →L[ℂ] F) (c : ℂ) (x : F) :
    rayleighVal T (c • x) = ‖c‖ ^ 2 * rayleighVal T x := by
  simp [rayleighVal, inner_smul_left, inner_smul_right, Complex.mul_re,
    Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem ritzG_singleSet (T : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    rayleighSetOn T (Submodule.span ℂ {x}) = {rayleighVal T x} := by
  ext r
  constructor
  · rintro ⟨y, hy, hy1, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc : ‖c‖ = 1 := by simpa [norm_smul, hx] using hy1
    simp [ritzG_smul, hc]
  · rintro rfl
    exact ⟨x, Submodule.mem_span_singleton_self x, hx, rfl⟩

private theorem ritzG_singleSup (T : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    rayleighSup T (Submodule.span ℂ {x}) = rayleighVal T x := by
  simp [rayleighSup, ritzG_singleSet T hx]

private theorem ritzG_zeroSet (T : F →L[ℂ] F) : minmaxSet T 0 = rayleighSet T := by
  ext r
  constructor
  · rintro ⟨S, hd, rfl⟩
    obtain ⟨_, x, hxS, hx, _⟩ := ritzP_ne T (show 0 < Module.finrank ℂ S by omega)
    have hx0 : x ≠ 0 := by intro he; simp [he] at hx
    have hs : S = Submodule.span ℂ {x} :=
      eq_span_singleton_of_mem_of_finrank_eq_one (by simpa using hd) hxS hx0
    exact ⟨x, hx, by rw [hs, ritzG_singleSup T hx]; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := by intro he; simp [he] at hx
    exact ⟨Submodule.span ℂ {x}, by simpa using finrank_span_singleton hx0,
      (ritzG_singleSup T hx).symm⟩

private theorem ritzG_mono (T : F →L[ℂ] F) {k l : ℕ} (hkl : k ≤ l)
    (hne : (minmaxSet T l).Nonempty) : minmaxLevel T k ≤ minmaxLevel T l := by
  apply le_csInf hne
  rintro r ⟨S, hd, rfl⟩
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℂ) (M := S)
    (n := k + 1) (by omega)
  let S' : Submodule ℂ F := Submodule.span ℂ (Set.range fun i => (f i : F))
  have hd' : Module.finrank ℂ S' = k + 1 := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range (S.subtype ∘ f))) = k + 1
    rw [finrank_span_eq_card (hf.map' S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective))]
    exact Fintype.card_fin (k + 1)
  have hsub : S' ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f i).property
  have hsup : rayleighSup T S' ≤ rayleighSup T S := by
    apply csSup_le (ritzP_ne T (show 0 < Module.finrank ℂ S' by omega))
    rintro r ⟨x, hxS, hx, rfl⟩
    exact le_csSup (ritzR_bddAbove T S) ⟨x, hsub hxS, hx, rfl⟩
  exact (csInf_le (ritzR_bddBelow T k) ⟨S', hd', rfl⟩).trans hsup

private theorem ritzG_dim (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    Module.finrank ℂ (galerkinSpan b m) = m := by
  have he : b '' {i | i < m} = Set.range (fun i : Fin m => b i) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.isLt, rfl⟩
  have hi := b.orthonormal.linearIndependent.comp (fun i : Fin m => (i : ℕ)) Fin.val_injective
  unfold galerkinSpan
  rw [he]
  simpa only [Function.comp_def, Fintype.card_fin] using finrank_span_eq_card hi

private theorem ritzG_neIn (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {k m : ℕ}
    (hm : k + 1 ≤ m) : (minmaxSetIn T (galerkinSpan b m) k).Nonempty := by
  refine ⟨rayleighSup T (galerkinSpan b (k + 1)), galerkinSpan b (k + 1), ?_,
    ritzG_dim b (k + 1), rfl⟩
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  exact Nat.lt_of_lt_of_le hi hm

-- Adapted from leonardopedro/timepiece at commit 61595bc, ChapterSirkRitzMinMax.lean.
private theorem ritzG_valSub (T : F →L[ℂ] F) (y u : F) :
    rayleighVal T y - rayleighVal T u ≤ ‖T‖ * (‖y‖ + ‖u‖) * ‖y - u‖ := by
  have hsplit : (inner ℂ y (T y) : ℂ) - inner ℂ u (T u)
      = inner ℂ (y - u) (T y) + inner ℂ u (T (y - u)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h1 : rayleighVal T y - rayleighVal T u
      = (inner ℂ (y - u) (T y) : ℂ).re + (inner ℂ u (T (y - u)) : ℂ).re := by
    rw [rayleighVal, rayleighVal, ← Complex.sub_re, hsplit, Complex.add_re]
  have hb1 : (inner ℂ (y - u) (T y) : ℂ).re ≤ ‖y - u‖ * (‖T‖ * ‖y‖) := by
    calc (inner ℂ (y - u) (T y) : ℂ).re ≤ ‖(inner ℂ (y - u) (T y) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖y - u‖ * ‖T y‖ := norm_inner_le_norm _ _
      _ ≤ ‖y - u‖ * (‖T‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
  have hb2 : (inner ℂ u (T (y - u)) : ℂ).re ≤ ‖u‖ * (‖T‖ * ‖y - u‖) := by
    calc (inner ℂ u (T (y - u)) : ℂ).re ≤ ‖(inner ℂ u (T (y - u)) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖u‖ * ‖T (y - u)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖T‖ * ‖y - u‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
  rw [h1]
  nlinarith [hb1, hb2]


-- Adapted from Leonardo Pedro, timepiece commit 61595bc, ChapterSirkRitzSpectrum.lean (Apache-2.0).
open RCLike ContinuousLinearMap ComplexOrder Pointwise

private theorem ritzS_selfAdjoint_re_inner_coe (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (x : F) :
    (((inner ℂ (T x) x : ℂ).re : ℝ) : ℂ) = inner ℂ (T x) x := by
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) x x
  refine Complex.conj_eq_iff_re.mp ?_
  rw [inner_conj_symm]
  exact hsym.symm

private theorem ritzS_re_inner_comm (T : F →L[ℂ] F) (x : F) :
    (inner ℂ (T x) x : ℂ).re = (inner ℂ x (T x) : ℂ).re := by
  have h : (starRingEnd ℂ) (inner ℂ x (T x)) = inner ℂ (T x) x := inner_conj_symm _ _
  rw [← h, Complex.conj_re]

private theorem ritzS_re_inner_sub_algebraMap (T : F →L[ℂ] F) (c : ℝ) (x : F) :
    (inner ℂ ((T - (algebraMap ℝ (F →L[ℂ] F)) c) x) x : ℂ).re
      = (inner ℂ (T x) x : ℂ).re - c * ‖x‖ ^ 2 := by
  have h : (T - (algebraMap ℝ (F →L[ℂ] F)) c) x = T x - (c : ℂ) • x := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h, inner_sub_left, Complex.sub_re, inner_smul_left]
  simp [Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

private theorem ritzS_le_rayleigh_iff_le_spectrum (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (c : ℝ) :
    (∀ x : F, c * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re) ↔ ∀ μ ∈ spectrum ℝ T, c ≤ μ := by
  have hS : IsSelfAdjoint (T - (algebraMap ℝ (F →L[ℂ] F)) c) :=
    hT.sub (IsSelfAdjoint.algebraMap (F →L[ℂ] F) rfl)
  have hmain := StarOrderedRing.nonneg_iff_spectrum_nonneg
    (R := ℝ) (T - (algebraMap ℝ (F →L[ℂ] F)) c) hS
  have hpos : (0 ≤ T - (algebraMap ℝ (F →L[ℂ] F)) c) ↔
      ∀ x : F, c * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re := by
    rw [nonneg_iff_isPositive, isPositive_iff_complex]
    constructor
    · intro h x
      have h2 := (h x).2
      rw [RCLike.re_to_complex, ritzS_re_inner_sub_algebraMap T c x] at h2
      rw [← ritzS_re_inner_comm]
      linarith
    · intro h x
      refine ⟨by simpa only [RCLike.re_to_complex] using ritzS_selfAdjoint_re_inner_coe _ hS x, ?_⟩
      rw [RCLike.re_to_complex, ritzS_re_inner_sub_algebraMap T c x, ritzS_re_inner_comm]
      linarith [h x]
  have hspec : spectrum ℝ (T - (algebraMap ℝ (F →L[ℂ] F)) c) = spectrum ℝ T - {c} :=
    (spectrum.sub_singleton_eq T c).symm
  rw [← hpos, hmain]
  constructor
  · intro h μ hμ
    have := h (μ - c) (by rw [hspec]; exact ⟨μ, hμ, c, rfl, rfl⟩)
    linarith
  · intro h ν hν
    rw [hspec] at hν
    obtain ⟨μ, hμ, d, hd, rfl⟩ := hν
    simp only [Set.mem_singleton_iff] at hd
    subst hd
    linarith [h μ hμ]

private theorem ritzS_abs_re_inner_le (T : F →L[ℂ] F) (x : F) :
    |(inner ℂ x (T x) : ℂ).re| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc |(inner ℂ x (T x) : ℂ).re| ≤ ‖(inner ℂ x (T x) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

private theorem ritzS_re_inner_le_norm (T : F →L[ℂ] F) (x : F) :
    (inner ℂ x (T x) : ℂ).re ≤ ‖T‖ * ‖x‖ ^ 2 :=
  (le_abs_self _).trans (ritzS_abs_re_inner_le T x)

private theorem ritzS_neg_norm_le_re_inner (T : F →L[ℂ] F) (x : F) :
    -(‖T‖ * ‖x‖ ^ 2) ≤ (inner ℂ x (T x) : ℂ).re :=
  neg_le_of_abs_le (ritzS_abs_re_inner_le T x)

private theorem ritzS_spectrum_real_nonempty [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    (spectrum ℝ T).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  set x : F := ‖y‖⁻¹ • y with hx
  have hxnorm : ‖x‖ = 1 := by
    rw [hx, norm_smul]
    simp [norm_ne_zero_iff.mpr hy]
  have hbound := (ritzS_le_rayleigh_iff_le_spectrum T hT (‖T‖ + 1)).mpr
    (by intro μ hμ; rw [hempty] at hμ; simp at hμ) x
  have hupper := ritzS_re_inner_le_norm T x
  rw [hxnorm] at hbound hupper
  norm_num at hbound hupper
  linarith

private theorem ritzS_spectrum_real_bddBelow (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    BddBelow (spectrum ℝ T) := by
  refine ⟨-‖T‖, ?_⟩
  intro μ hμ
  refine (ritzS_le_rayleigh_iff_le_spectrum T hT (-‖T‖)).mp ?_ μ hμ
  intro x
  have := ritzS_neg_norm_le_re_inner T x
  linarith

private theorem ritzS_rayleighSet_nonempty [Nontrivial F] (T : F →L[ℂ] F) : (rayleighSet T).Nonempty := by
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine ⟨_, ‖y‖⁻¹ • y, ?_, rfl⟩
  rw [norm_smul]
  simp [norm_ne_zero_iff.mpr hy]

private theorem ritzS_rayleighSet_bddBelow (T : F →L[ℂ] F) : BddBelow (rayleighSet T) := by
  refine ⟨-‖T‖, ?_⟩
  rintro t ⟨x, hx1, rfl⟩
  have := ritzS_neg_norm_le_re_inner T x
  rw [hx1] at this
  simpa using this

private theorem ritzS_re_inner_real_smul (T : F →L[ℂ] F) (c : ℝ) (x : F) :
    (inner ℂ ((c : ℂ) • x) (T ((c : ℂ) • x)) : ℂ).re = c ^ 2 * (inner ℂ x (T x) : ℂ).re := by
  rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, sq]

private theorem ritzS_rayleighInf_mul_normSq_le [Nontrivial F] (T : F →L[ℂ] F) (x : F) :
    rayleighInf T * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    set u : F := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul]
      simp [hxpos.ne']
    have hmem : (inner ℂ u (T u) : ℂ).re ∈ rayleighSet T := ⟨u, hunorm, rfl⟩
    have hle : rayleighInf T ≤ (inner ℂ u (T u) : ℂ).re :=
      csInf_le (ritzS_rayleighSet_bddBelow T) hmem
    have hval : (inner ℂ u (T u) : ℂ).re = ‖x‖⁻¹ ^ 2 * (inner ℂ x (T x) : ℂ).re := by
      rw [hu, ritzS_re_inner_real_smul T (‖x‖⁻¹) x]
    rw [hval] at hle
    have hsq : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hle (le_of_lt hsq)
    calc rayleighInf T * ‖x‖ ^ 2 ≤ ‖x‖⁻¹ ^ 2 * (inner ℂ x (T x) : ℂ).re * ‖x‖ ^ 2 := this
      _ = (inner ℂ x (T x) : ℂ).re := by
          field_simp

private theorem ritzS_sInf_spectrum_eq_rayleighInf [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    sInf (spectrum ℝ T) = rayleighInf T := by
  have hspecne := ritzS_spectrum_real_nonempty T hT
  have hspecbdd := ritzS_spectrum_real_bddBelow T hT
  refine le_antisymm ?_ ?_
  · -- every Rayleigh quotient dominates the bottom of the spectrum
    refine le_csInf (ritzS_rayleighSet_nonempty T) ?_
    rintro t ⟨x, hx1, rfl⟩
    have hlb : ∀ μ ∈ spectrum ℝ T, sInf (spectrum ℝ T) ≤ μ := fun μ hμ => csInf_le hspecbdd hμ
    have := (ritzS_le_rayleigh_iff_le_spectrum T hT (sInf (spectrum ℝ T))).mpr hlb x
    rwa [hx1, one_pow, mul_one] at this
  · -- and the bottom of the numerical range is a lower bound for the spectrum
    refine le_csInf hspecne ?_
    intro μ hμ
    exact (ritzS_le_rayleigh_iff_le_spectrum T hT (rayleighInf T)).mp
      (ritzS_rayleighInf_mul_normSq_le T) μ hμ

theorem solution [Nontrivial F] (T T' : F →L[ℂ] F)
    (hT : IsSelfAdjoint T) (hT' : IsSelfAdjoint T')
    (hne : (minmaxSet T 0).Nonempty) :
    |sInf (spectrum ℝ T) - sInf (spectrum ℝ T')| ≤ ‖T - T'‖ := by
  have h0 : minmaxLevel T 0 = rayleighInf T := by
    unfold minmaxLevel rayleighInf
    rw [ritzG_zeroSet T]
  have h1 : minmaxLevel T' 0 = rayleighInf T' := by
    unfold minmaxLevel rayleighInf
    rw [ritzG_zeroSet T']
  rw [ritzS_sInf_spectrum_eq_rayleighInf T hT, ritzS_sInf_spectrum_eq_rayleighInf T' hT', ← h0, ← h1]
  exact ritzP_absLevel T T' 0 hne

#print axioms solution
