-- Prove2me | solution 1 for BookProof.BandEnclosure.ritz_band_enclosure_of_nested
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:33:44.533039+00:00
-- url     : https://prove2.me/submissions/a2e14595-1873-4ead-9ea2-3923d5ba5615

import Definitions.Def_ChapterBandEnclosure
-- Adapted from Leonardo Pedro, timepiece 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SirkFiniteAux
open BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin BookProof.FarisLavine
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem finiteModeDomain_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((finiteModeDomain b : Submodule ℂ F) : Set F) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span

private theorem abs_re_inner_le (T : F →L[ℂ] F) (x : F) :
    |(inner ℂ x (T x) : ℂ).re| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc |(inner ℂ x (T x) : ℂ).re| ≤ ‖(inner ℂ x (T x) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

private theorem neg_norm_le_re_inner (T : F →L[ℂ] F) (x : F) :
    -(‖T‖ * ‖x‖ ^ 2) ≤ (inner ℂ x (T x) : ℂ).re :=
  neg_le_of_abs_le (abs_re_inner_le T x)

private theorem rayleighSet_nonempty [Nontrivial F] (T : F →L[ℂ] F) : (rayleighSet T).Nonempty := by
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine ⟨_, ‖y‖⁻¹ • y, ?_, rfl⟩
  rw [norm_smul]
  simp [norm_ne_zero_iff.mpr hy]

private theorem rayleighSet_bddBelow (T : F →L[ℂ] F) : BddBelow (rayleighSet T) := by
  refine ⟨-‖T‖, ?_⟩
  rintro t ⟨x, hx1, rfl⟩
  have := neg_norm_le_re_inner T x
  rw [hx1] at this
  simpa using this

private theorem ritzSet_subset_rayleighSet (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    ritzSet (finiteModeRestrict A b) (finiteModeDomain b) ⊆ rayleighSet A := by
  rintro t ⟨x, -, hx1, rfl⟩
  exact ⟨(x : F), hx1, rfl⟩

private theorem ritzSet_finiteModeRestrict_eq (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    ritzSet (finiteModeRestrict A b) (finiteModeDomain b) =
      {t : ℝ | ∃ u : F, u ∈ finiteModeDomain b ∧ ‖u‖ = 1 ∧ t = (inner ℂ u (A u) : ℂ).re} := by
  ext t
  constructor
  · rintro ⟨x, -, hx1, rfl⟩
    exact ⟨(x : F), x.2, hx1, rfl⟩
  · rintro ⟨u, hu, hu1, rfl⟩
    exact ⟨⟨u, hu⟩, hu, hu1, rfl⟩

private theorem ritzSet_finiteModeRestrict_bddBelow (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    BddBelow (ritzSet (finiteModeRestrict A b) (finiteModeDomain b)) :=
  (rayleighSet_bddBelow A).mono (ritzSet_subset_rayleighSet A b)

private theorem ritzInf_finiteModeDomain_le (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    {x : F} (hx1 : ‖x‖ = 1) :
    ritzInf (finiteModeRestrict A b) (finiteModeDomain b) ≤ (inner ℂ x (A x) : ℂ).re := by
  have hbdd := ritzSet_finiteModeRestrict_bddBelow A b
  rw [ritzSet_finiteModeRestrict_eq A b] at hbdd
  change sInf (ritzSet (finiteModeRestrict A b) (finiteModeDomain b)) ≤ _
  rw [ritzSet_finiteModeRestrict_eq A b]
  set S : Submodule ℂ F := finiteModeDomain b with hS
  have hdense : Dense (S : Set F) := finiteModeDomain_dense b
  have hf : Continuous (fun z : F => (inner ℂ z (A z) : ℂ).re) := by fun_prop
  choose y hymem hydist using
    fun n : ℕ => Metric.mem_closure_iff.mp (hdense x) (1 / (n + 1)) (by positivity)
  have hy : Tendsto y atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]
    exact (hydist n).le
  have hnorm : Tendsto (fun n => ‖y n‖) atTop (nhds 1) := by
    simpa [Function.comp_def, hx1] using (continuous_norm.continuousAt.tendsto.comp hy)
  set u : ℕ → F := fun n => ‖y n‖⁻¹ • y n with hu
  have hutend : Tendsto u atTop (nhds x) := by
    have h1 : Tendsto (fun n => ‖y n‖⁻¹) atTop (nhds 1) := by
      simpa using hnorm.inv₀ (by norm_num)
    have := h1.smul hy
    simpa [hu] using this
  have hev : ∀ᶠ n in atTop, ‖u n‖ = 1 := by
    have hpos : ∀ᶠ n in atTop, (0 : ℝ) < ‖y n‖ := hnorm.eventually_const_lt (by norm_num)
    filter_upwards [hpos] with n hn
    rw [hu]
    simp [norm_smul, hn.ne']
  have hle : ∀ᶠ n in atTop, sInf {t : ℝ | ∃ w : F, w ∈ S ∧ ‖w‖ = 1 ∧
      t = (inner ℂ w (A w) : ℂ).re} ≤ (inner ℂ (u n) (A (u n)) : ℂ).re := by
    filter_upwards [hev] with n hn
    exact csInf_le hbdd ⟨u n, S.smul_mem _ (hymem n), hn, rfl⟩
  exact ge_of_tendsto ((hf.tendsto x).comp hutend) hle

private theorem ritzInf_finiteModeDomain_eq_rayleighInf [Nontrivial F] (A : F →L[ℂ] F)
    (b : HilbertBasis ℕ ℂ F) :
    ritzInf (finiteModeRestrict A b) (finiteModeDomain b) = rayleighInf A := by
  refine le_antisymm ?_ ?_
  · refine le_csInf (rayleighSet_nonempty A) ?_
    rintro t ⟨x, hx1, rfl⟩
    exact ritzInf_finiteModeDomain_le A b hx1
  · refine csInf_le_csInf (rayleighSet_bddBelow A) ?_ (ritzSet_subset_rayleighSet A b)
    exact ⟨(inner ℂ (b 0) (A (b 0)) : ℂ).re, ⟨⟨b 0, Submodule.subset_span ⟨0, rfl⟩⟩,
      Submodule.subset_span ⟨0, rfl⟩, b.orthonormal.1 0, rfl⟩⟩

end SirkFiniteAux

namespace SirkBandSpectralAux
open BookProof.ChapterSirkRitzSpectrum Filter Topology
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

end SirkBandSpectralAux
namespace SirkBandRitzAux
open BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.BandEnclosure
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {D : Submodule ℂ F}

private theorem galerkinSpan_mono (b : HilbertBasis ℕ ℂ F) {m n : ℕ} (hmn : m ≤ n) :
    galerkinSpan b m ≤ galerkinSpan b n :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi hmn)

private theorem basis_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : i < m) :
    b i ∈ galerkinSpan b m :=
  Submodule.subset_span ⟨i, him, rfl⟩

private theorem galerkinSpan_le_finiteModeDomain (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ≤ finiteModeDomain b :=
  Submodule.span_mono (by rintro x ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)

private theorem finiteModeDomain_eq_iSup (b : HilbertBasis ℕ ℂ F) :
    finiteModeDomain b = ⨆ m : ℕ, galerkinSpan b m := by
  refine le_antisymm ?_ (iSup_le fun m => galerkinSpan_le_finiteModeDomain b m)
  rw [finiteModeDomain, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (i + 1) (basis_mem_galerkinSpan b (Nat.lt_succ_self i))

private theorem exists_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {x : F} (hx : x ∈ finiteModeDomain b) :
    ∃ m : ℕ, x ∈ galerkinSpan b m := by
  rw [finiteModeDomain_eq_iSup] at hx
  have hmono : Monotone (fun m : ℕ => galerkinSpan b m) := fun _ _ h => galerkinSpan_mono b h
  have hdir : Directed (· ≤ ·) (fun m : ℕ => galerkinSpan b m) := hmono.directed_le
  exact (Submodule.mem_iSup_of_directed _ hdir).mp hx

private theorem ritzSet_mono (H : D →ₗ[ℂ] F) {V W : Submodule ℂ F} (hVW : V ≤ W) :
    ritzSet H V ⊆ ritzSet H W := by
  rintro t ⟨x, hxV, hx1, rfl⟩
  exact ⟨x, hVW hxV, hx1, rfl⟩

private theorem ritzSet_bddBelow (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    (V : Submodule ℂ F) : BddBelow (ritzSet H V) := by
  refine ⟨0, ?_⟩
  rintro t ⟨x, _, _, rfl⟩
  exact hpos x

private theorem ritzInf_antitone (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    {V W : Submodule ℂ F} (hVW : V ≤ W) (hV : (ritzSet H V).Nonempty) :
    ritzInf H W ≤ ritzInf H V :=
  csInf_le_csInf (ritzSet_bddBelow H hpos W) hV (ritzSet_mono H hVW)

private theorem ritzInf_nonneg (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    (V : Submodule ℂ F) (hV : (ritzSet H V).Nonempty) : 0 ≤ ritzInf H V :=
  le_csInf hV (by rintro t ⟨x, _, _, rfl⟩; exact hpos x)

private theorem ritzInf_tendsto_domainInf (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) :
    Tendsto (fun m : ℕ => ritzInf H (galerkinSpan b (m + 1))) atTop
      (nhds (ritzInf H (finiteModeDomain b))) := by
  set a : ℕ → ℝ := fun m => ritzInf H (galerkinSpan b (m + 1)) with ha
  -- the first basis vector is a unit vector of every truncation subspace
  have hb0mem : b 0 ∈ finiteModeDomain b := Submodule.subset_span ⟨0, rfl⟩
  have hb0norm : ‖b 0‖ = 1 := b.orthonormal.1 0
  have hne : ∀ m : ℕ, (ritzSet H (galerkinSpan b (m + 1))).Nonempty := by
    intro m
    refine ⟨quadForm H ⟨b 0, hb0mem⟩, ⟨b 0, hb0mem⟩, ?_, hb0norm, rfl⟩
    exact galerkinSpan_mono b (Nat.succ_le_succ (Nat.zero_le m))
      (basis_mem_galerkinSpan b Nat.zero_lt_one)
  have hsub : ∀ m : ℕ, ritzSet H (galerkinSpan b (m + 1)) ⊆ ritzSet H (finiteModeDomain b) :=
    fun m => ritzSet_mono H (galerkinSpan_le_finiteModeDomain b (m + 1))
  -- the sequence of Ritz values is antitone and bounded below
  have hanti : Antitone a := by
    intro p q hpq
    exact ritzInf_antitone H hpos (galerkinSpan_mono b (Nat.succ_le_succ hpq)) (hne p)
  have hnonneg : ∀ m : ℕ, 0 ≤ a m := fun m => ritzInf_nonneg H hpos _ (hne m)
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro t ⟨m, rfl⟩; exact hnonneg m⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  -- and its limit is the infimum of the energy over the whole domain
  have hSne : (ritzSet H (finiteModeDomain b)).Nonempty := (hne 0).mono (hsub 0)
  have hkey : (⨅ m : ℕ, a m) = ritzInf H (finiteModeDomain b) := by
    refine le_antisymm ?_ ?_
    · refine le_csInf hSne ?_
      rintro t ⟨x, _, hx1, rfl⟩
      obtain ⟨m, hm⟩ := exists_mem_galerkinSpan b x.2
      have hmem : quadForm H x ∈ ritzSet H (galerkinSpan b (m + 1)) :=
        ⟨x, galerkinSpan_mono b (Nat.le_succ m) hm, hx1, rfl⟩
      refine le_trans (ciInf_le hbdd m) ?_
      exact csInf_le (ritzSet_bddBelow H hpos _) hmem
    · refine le_ciInf fun m => ?_
      exact csInf_le_csInf (ritzSet_bddBelow H hpos _) (hne m) (hsub m)
  rw [← hkey]
  exact hlim

private theorem nestedBands_le {lo hi : ℕ → ℝ} (h : NestedBands lo hi) {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact (h n).trans ih

private theorem band_enclosure_of_nested {lo hi a : ℕ → ℝ} {lam : ℝ}
    (hnest : NestedBands lo hi) (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m))
    (hconv : Tendsto a atTop (𝓝 lam)) :
    ∀ m, lam ∈ Set.Icc (lo m) (hi m) := by
  intro m
  have hev : ∀ᶠ n in atTop, a n ∈ Set.Icc (lo m) (hi m) := by
    filter_upwards [eventually_ge_atTop m] with n hn
    exact nestedBands_le hnest hn (hmem n)
  exact ⟨ge_of_tendsto hconv (hev.mono fun _ hn => hn.1),
    le_of_tendsto hconv (hev.mono fun _ hn => hn.2)⟩

end SirkBandRitzAux

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.ritz_band_enclosure_of_nested
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open BookProof.FarisLavine
theorem solution [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A)
    (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F)
    {lo hi : ℕ → ℝ} (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1)) ∈
      Set.Icc (lo m) (hi m)) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (lo m) (hi m) := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun x => ⟨by trivial, rfl⟩, ?_, fun y => hpos y, ?_⟩
    · intro x y
      exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) (x : F) (y : F)
    · intro w u hu
      refine ⟨by trivial, ?_⟩
      change A w = u
      apply ext_inner_left ℂ
      intro v
      have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) v w
      exact hs.symm.trans (hu ⟨v, by trivial⟩)
  · apply SirkBandRitzAux.band_enclosure_of_nested hnest hritz
    have hp : ∀ x : finiteModeDomain b, 0 ≤ quadForm (finiteModeRestrict A b) x := fun x => hpos x
    have hlim := SirkBandRitzAux.ritzInf_tendsto_domainInf b (finiteModeRestrict A b) hp
    rw [SirkBandSpectralAux.ritzS_sInf_spectrum_eq_rayleighInf A hsa,
      ← SirkFiniteAux.ritzInf_finiteModeDomain_eq_rayleighInf A b]
    exact hlim
#print axioms solution
