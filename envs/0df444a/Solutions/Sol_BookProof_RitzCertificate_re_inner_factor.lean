-- Prove2me | solution 1 for BookProof.RitzCertificate.re_inner_factor
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:30:25.946414+00:00
-- url     : https://prove2.me/submissions/3a628de3-0158-44b3-81e8-f028875fd186

import Definitions.Def_ChapterRitzCertificate
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SirkTempleAux
open BookProof.RitzCertificate BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
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

private theorem norm_apply_sq (A : F →L[ℂ] F) (x : F) (hx : ‖x‖ = 1) :
    ‖A x‖ ^ 2 = resid A x ^ 2 + rayleigh A x ^ 2 := by
  have hsym : (inner ℂ (A x) x : ℂ).re = (inner ℂ x (A x) : ℂ).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) x (A x), Complex.conj_re]
  have h := @norm_sub_sq ℂ F _ _ _ (A x) (((rayleigh A x : ℝ) : ℂ) • x)
  rw [resid, h, inner_smul_right, norm_smul]
  simp only [rayleigh, RCLike.mul_re, RCLike.re_to_complex, Complex.ofReal_re,
    RCLike.im_to_complex, Complex.ofReal_im, zero_mul, sub_zero, Complex.norm_real,
    Real.norm_eq_abs, hx, mul_one, sq_abs]
  rw [hsym]
  ring

private theorem isSelfAdjoint_sub_const {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (c : ℝ) :
    IsSelfAdjoint (A - (c : ℝ) • (1 : F →L[ℂ] F)) := by
  simp [IsSelfAdjoint, star_sub, hA.star_eq]

private theorem re_inner_factor {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (l b : ℝ) (x : F) :
    (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) *
        (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ).re
      = ‖A x‖ ^ 2 - (l + b) * rayleigh A x + l * b * ‖x‖ ^ 2 := by
  have hsym : (inner ℂ (A x) x : ℂ).re = (inner ℂ x (A x) : ℂ).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) x (A x), Complex.conj_re]
  have hPx : (A - (l : ℝ) • (1 : F →L[ℂ] F)) x = A x - (l : ℂ) • x := by simp
  have hQx : (A - (b : ℝ) • (1 : F →L[ℂ] F)) x = A x - (b : ℂ) • x := by simp
  have hmove : (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) *
        (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ)
      = inner ℂ ((A - (l : ℝ) • (1 : F →L[ℂ] F)) x)
          ((A - (b : ℝ) • (1 : F →L[ℂ] F)) x) := by
    rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
      (isSelfAdjoint_sub_const hA l).adjoint_eq]
  rw [hmove, hPx, hQx, rayleigh]
  simp [inner_self_eq_norm_sq_to_K, Complex.sub_re, Complex.mul_re, hsym,
    ← Complex.ofReal_pow]
  ring_nf

private theorem factor_nonneg {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ}
    (hspec : ∀ t ∈ spectrum ℝ A, 0 ≤ (t - l) * (t - b)) :
    0 ≤ (A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F)) := by
  have h1 : cfc (fun t : ℝ => (t - l) * (t - b)) A
      = (A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F)) := by
    rw [cfc_mul _ _ A, cfc_sub _ _ A, cfc_sub _ _ A, cfc_id' ℝ A, cfc_const l A, cfc_const b A,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rw [← h1]
  exact cfc_nonneg hspec

private theorem factor_nonneg_of_separation {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ}
    (hsep : SpectralSeparation A l b) :
    0 ≤ (A - (l : ℝ) • (1 : F →L[ℂ] F)) * (A - (b : ℝ) • (1 : F →L[ℂ] F)) := by
  refine factor_nonneg hA ?_
  intro t ht
  rcases hsep.2 t ht with h | h
  · simp [h]
  · have h1 : 0 ≤ t - l := by linarith [hsep.1]
    have h2 : 0 ≤ t - b := by linarith
    positivity

private theorem temple_lower_bound {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {l b : ℝ} {x : F}
    (hsep : SpectralSeparation A l b) (hx : ‖x‖ = 1) (hlt : rayleigh A x < b) :
    rayleigh A x - resid A x ^ 2 / (b - rayleigh A x) ≤ l := by
  set th := rayleigh A x with hth
  set eps := resid A x with heps
  have hpos := factor_nonneg_of_separation hA hsep
  have hquad0 := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos).inner_nonneg_right x
  have hquad : 0 ≤ (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) *
      (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ).re := by
    simpa only [Complex.zero_re] using (Complex.le_def.mp hquad0).1
  rw [re_inner_factor hA l b x, norm_apply_sq A x hx, hx] at hquad
  have hkey : (th - l) * (b - th) ≤ eps ^ 2 := by nlinarith [hquad]
  have hbth : 0 < b - th := by linarith
  have hdiv : th - l ≤ eps ^ 2 / (b - th) := (le_div_iff₀ hbth).mpr hkey
  linarith

private theorem sInf_spectrum_le_rayleigh [Nontrivial F] (A : F →L[ℂ] F) (hA : IsSelfAdjoint A)
    {x : F} (hx : ‖x‖ = 1) : sInf (spectrum ℝ A) ≤ rayleigh A x := by
  have h := ritzS_rayleighInf_mul_normSq_le A x
  rw [hx] at h
  rw [ritzS_sInf_spectrum_eq_rayleighInf A hA, rayleigh]
  simpa using h

private theorem temple_width_tendsto_zero {A : F →L[ℂ] F} {b delta : ℝ} {x : ℕ → F}
    (hdelta : 0 < delta) (hle : ∀ m, rayleigh A (x m) ≤ b - delta)
    (hres : Tendsto (fun m => resid A (x m)) atTop (𝓝 0)) :
    Tendsto (fun m => rayleigh A (x m) -
      (rayleigh A (x m) - resid A (x m) ^ 2 / (b - rayleigh A (x m)))) atTop (𝓝 0) := by
  have hsq : Tendsto (fun m => resid A (x m) ^ 2) atTop (𝓝 0) := by
    simpa using hres.pow 2
  have hsqueeze : ∀ m, |rayleigh A (x m) -
      (rayleigh A (x m) - resid A (x m) ^ 2 / (b - rayleigh A (x m)))|
        ≤ resid A (x m) ^ 2 / delta := by
    intro m
    have hb : delta ≤ b - rayleigh A (x m) := by linarith [hle m]
    have hnn : 0 ≤ resid A (x m) ^ 2 := sq_nonneg _
    have : resid A (x m) ^ 2 / (b - rayleigh A (x m)) ≤ resid A (x m) ^ 2 / delta :=
      div_le_div_of_nonneg_left hnn hdelta hb
    have hpos : 0 ≤ resid A (x m) ^ 2 / (b - rayleigh A (x m)) :=
      div_nonneg hnn (by linarith)
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hbound : Tendsto (fun m => resid A (x m) ^ 2 / delta) atTop (𝓝 0) := by
    simpa using hsq.div_const delta
  exact squeeze_zero_norm hsqueeze hbound

end SirkTempleAux

-- Generated from ChapterRitzCertificate.lean — theorem BookProof.RitzCertificate.re_inner_factor
open BookProof.RitzCertificate













noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterSirkRitzSpectrum BookProof.BandEnclosure


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open SirkTempleAux

theorem solution {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (l b : ℝ) (x : F) :
    (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) *
        (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ).re
      = ‖A x‖ ^ 2 - (l + b) * rayleigh A x + l * b * ‖x‖ ^ 2 := by
  have hsym : (inner ℂ (A x) x : ℂ).re = (inner ℂ x (A x) : ℂ).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) x (A x), Complex.conj_re]
  have hPx : (A - (l : ℝ) • (1 : F →L[ℂ] F)) x = A x - (l : ℂ) • x := by simp
  have hQx : (A - (b : ℝ) • (1 : F →L[ℂ] F)) x = A x - (b : ℂ) • x := by simp
  have hmove : (inner ℂ x ((((A - (l : ℝ) • (1 : F →L[ℂ] F)) *
        (A - (b : ℝ) • (1 : F →L[ℂ] F))) x)) : ℂ)
      = inner ℂ ((A - (l : ℝ) • (1 : F →L[ℂ] F)) x)
          ((A - (b : ℝ) • (1 : F →L[ℂ] F)) x) := by
    rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
      (isSelfAdjoint_sub_const hA l).adjoint_eq]
  rw [hmove, hPx, hQx, rayleigh]
  simp [inner_self_eq_norm_sq_to_K, Complex.sub_re, Complex.mul_re, hsym,
    ← Complex.ofReal_pow]
  ring_nf

#print axioms solution
