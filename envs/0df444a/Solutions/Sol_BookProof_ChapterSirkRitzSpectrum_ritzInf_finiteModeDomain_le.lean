-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:28:47.97573+00:00
-- url     : https://prove2.me/submissions/7ad41088-1039-451a-89eb-f5d11d45e45a

import Definitions.Def_ChapterSirkRitzSpectrum
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
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

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_le
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open SirkFiniteAux

theorem solution (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
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

#print axioms solution
