-- Prove2me | solution 1 for ConnesGreen.RG0Integration.sourceEmbed_L_energyVector
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:46:22.227412+00:00
-- url     : https://prove2.me/submissions/3b88ed04-5e88-467f-a76c-bb9d25001edb

import Definitions.Def_ConnesGreen_RG0_source_constructors
import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory Set ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical Topology Interval ComplexConjugate
noncomputable section
namespace WeilDefect
attribute [local instance 1100] NormedSpace.complexToReal
open Filter Set Bornology


































































end WeilDefect

namespace WeilDefect.ConnesNative
open WeilDefect










end WeilDefect.ConnesNative

namespace ConnesGreen


end ConnesGreen
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

/-- All continuous native sources and columns are valid L2 inputs on a finite
window, so the total extension used in the model is never invoked there. -/
theorem continuous_window_memLp (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (windowMeasure t) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc





theorem supported_energyDomain (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    EnergyDomain t g :=
  ⟨continuous_window_memLp _ _ hg.1.1.continuous,
    continuous_window_memLp _ _ (hg.1.1.continuous_iteratedDeriv 1 (by simp))⟩



theorem supported_energy_mem (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    energyVector t g ∈ energySubspace t := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨⟨g, hg⟩, rfl⟩



end ConnesGreen

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative



theorem windowL2_inner (t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure t)) (hg : MemLp g 2 (windowMeasure t)) :
    ⟪windowL2 t f, windowL2 t g⟫_ℂ =
      ∫ x, star (f x) * g x ∂windowMeasure t := by
  simp only [windowL2, dif_pos hf, dif_pos hg, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]



theorem supported_endpoints_zero (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    g t = 0 ∧ g (-t) = 0 := by
  constructor <;> by_contra hn
  · exact (lt_irrefl t) (hg.2 (subset_tsupport g hn)).2
  · exact (lt_irrefl (-t)) (hg.2 (subset_tsupport g hn)).1

theorem derivativeProbe_inner_energy (t : ℝ) (ht : 0 < t)
    (φ g : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hg : SupportedTest t g) :
    ⟪derivativeProbe t φ, energyVector t g⟫_ℂ = 0 := by
  have hφd : Continuous (iteratedDeriv 1 φ) :=
    hφ.continuous_iteratedDeriv 1 (by norm_num)
  have hgd : Continuous (iteratedDeriv 1 g) :=
    hg.1.1.continuous_iteratedDeriv 1 (by simp)
  have hφlp := continuous_window_memLp t φ hφ.continuous
  have hφdlp := continuous_window_memLp t _ hφd
  have hglp := (supported_energyDomain t g hg).1
  have hgdlp := (supported_energyDomain t g hg).2
  have hb := supported_endpoints_zero t g hg
  have hip := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := -t) (b := t) (u := fun x => star (φ x)) (v := g)
    (u' := fun x => star (iteratedDeriv 1 φ x)) (v' := iteratedDeriv 1 g)
    hφ.continuous.star.continuousOn hg.1.1.continuous.continuousOn
    (fun x _ => by simpa [iteratedDeriv_one] using
      (hφ.differentiable (by norm_num) x).hasDerivAt.star)
    (fun x _ => by simpa [iteratedDeriv_one] using
      (hg.1.1.differentiable (by simp) x).hasDerivAt)
    (hφd.star.intervalIntegrable _ _) (hgd.intervalIntegrable _ _)
  simp only [hb.1, hb.2, mul_zero, sub_zero] at hip
  have hi1 : Integrable (fun x => star (φ x) * iteratedDeriv 1 g x)
      (windowMeasure t) := (hφ.continuous.star.mul hgd).integrableOn_Icc
  have hi2 : Integrable (fun x => star (iteratedDeriv 1 φ x) * g x)
      (windowMeasure t) := (hφd.star.mul hg.1.1.continuous).integrableOn_Icc
  have hsum : (∫ x, star (φ x) * iteratedDeriv 1 g x +
      star (iteratedDeriv 1 φ x) * g x ∂windowMeasure t) = 0 := by
    unfold windowMeasure
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith : -t ≤ t)]
    convert hip using 1
    congr 1
    ext x
    ring
  have hinner : ⟪derivativeProbe t φ, energyVector t g⟫_ℂ =
      ⟪windowL2 t φ, windowL2 t (iteratedDeriv 1 g)⟫_ℂ +
      ⟪windowL2 t (iteratedDeriv 1 φ), windowL2 t g⟫_ℂ := by
    simp [derivativeProbe, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
      inner_smul_left, inner_smul_right, map_ofNat]
  rw [hinner, windowL2_inner t φ _ hφlp hgdlp,
    windowL2_inner t _ g hφdlp hglp, ← integral_add hi1 hi2]
  exact hsum





end ConnesGreen

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

theorem windowL2_L (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    windowL2 t (problemOneL g) = -windowL2 t (iteratedDeriv 2 g) +
      (1 / 4 : ℂ) • windowL2 t g := by
  have hf := continuous_window_memLp t _
    (hg.1.1.continuous_iteratedDeriv 2 (by norm_cast <;> simp))
  have hh := (supported_energyDomain t g hg).1
  change windowL2 t (-iteratedDeriv 2 g + (1 / 4 : ℂ) • g) = _
  simp only [windowL2, dif_pos hf, dif_pos hh,
    dif_pos (hf.neg.add (hh.const_smul (1 / 4 : ℂ))),
    MemLp.toLp_add, MemLp.toLp_neg, MemLp.toLp_const_smul]
  rfl

theorem sourceLoad_L_sub_energy_orthogonal (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    sourceLoad t (windowL2 t (problemOneL g)) - energyVector t g ∈ (energySubspace t)ᗮ := by
  let D := sourceLoad t (windowL2 t (problemOneL g)) - energyVector t g
  have hi : ∀ u : ℝ → ℂ, SupportedTest t u → ⟪energyVector t u, D⟫_ℂ = 0 := by
    intro u hu
    have hder : ContDiff ℝ 1 (iteratedDeriv 1 g) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv (n := 1)).mp
        (hg.1.1.of_le (by norm_cast <;> simp)) |>.2
    have hip := derivativeProbe_inner_energy t ht (iteratedDeriv 1 g) u hder hu
    have hid : iteratedDeriv 1 (iteratedDeriv 1 g) = iteratedDeriv 2 g := by
      simp [iteratedDeriv_succ, iteratedDeriv_one]
    have hip' : ⟪windowL2 t (iteratedDeriv 1 g), windowL2 t (iteratedDeriv 1 u)⟫_ℂ +
        ⟪windowL2 t (iteratedDeriv 2 g), windowL2 t u⟫_ℂ = 0 := by
      simpa [derivativeProbe, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
        inner_smul_left, inner_smul_right, map_ofNat,
        iteratedDeriv_succ, iteratedDeriv_one] using hip
    have hc := congrArg (starRingEnd ℂ) hip'
    simp only [map_add, map_zero, inner_conj_symm] at hc
    have hex : ⟪energyVector t u, D⟫_ℂ =
        -(⟪windowL2 t (iteratedDeriv 1 u), windowL2 t (iteratedDeriv 1 g)⟫_ℂ +
          ⟪windowL2 t u, windowL2 t (iteratedDeriv 2 g)⟫_ℂ) := by
      simp [D, sourceLoad, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
        inner_sub_right, windowL2_L t g hg, inner_add_right, inner_neg_right,
        inner_smul_left, inner_smul_right, map_ofNat]
      ring
    rw [hex, hc, neg_zero]
  have hs : energySubspace t ≤ (ℂ ∙ D)ᗮ := by
    unfold energySubspace
    apply Submodule.topologicalClosure_minimal _ _ (ℂ ∙ D).isClosed_orthogonal
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    exact hi u hu
  apply (energySubspace t).mem_orthogonal D |>.mpr
  intro u hu
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hs hu)

/-- The computed source embedding of Lg is exactly the original energy image
of g, in the same completed physical carrier. -/
theorem sourceEmbed_L (t : ℝ) (ht : 0 < t) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    sourceEmbed t (problemOneL g) =
      (⟨energyVector t g, supported_energy_mem t g hg⟩ : Physical t) := by
  let e : Physical t := ⟨energyVector t g, supported_energy_mem t g hg⟩
  have hz := (energySubspace t).orthogonalProjectionOnto_eq_zero_iff.mpr
    (sourceLoad_L_sub_energy_orthogonal t ht g hg)
  change (energySubspace t).orthogonalProjectionOnto
    (sourceLoad t (windowL2 t (problemOneL g)) - (e : Ambient t)) = 0 at hz
  rw [map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hz
  exact sub_eq_zero.mp hz





end ConnesGreen



open ConnesGreen WeilDefect WeilDefect.ConnesNative
theorem solution (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    (sourceEmbed t (problemOneL g) : Ambient t) = energyVector t g := by
  exact congrArg (fun x : Physical t => (x : Ambient t)) (ConnesGreen.sourceEmbed_L t ht g hg)
