-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.real_affine_integral_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:15:12.704585+00:00
-- url     : https://prove2.me/submissions/24997968-d209-4cfd-9f44-6aa88e2abe1d

import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology

namespace EulerNormWork

lemma integral_norm_lower_bound {K : Type*} [Field K] [NumberField K]
    (u : K) (hu : IsIntegral ℤ u) (hne : u ≠ 0) :
    1 ≤ ‖((Algebra.norm ℚ u : ℚ) : ℂ)‖ := by
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm ℚ hu)
  have hm0 : m ≠ 0 := by
    intro h
    have : Algebra.norm ℚ u = 0 := by simpa [h] using hm.symm
    exact (Algebra.norm_ne_zero_iff.mpr hne) this
  rw [← hm]
  simpa using (show (1 : ℝ) ≤ |(m : ℝ)| by exact_mod_cast Int.one_le_abs hm0)

lemma affine_integral_eventually_zero {K : Type*} [Field K] [NumberField K]
    (a : K) (r s : ℕ → ℚ)
    (hr : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 0))
    (hs : Tendsto (fun n => (s n : ℂ)) atTop (𝓝 0))
    (hi : ∀ n, IsIntegral ℤ (algebraMap ℚ K (r n) * a + algebraMap ℚ K (s n))) :
    ∀ᶠ n in atTop, algebraMap ℚ K (r n) * a + algebraMap ℚ K (s n) = 0 := by
  classical
  let u : ℕ → K := fun n => algebraMap ℚ K (r n) * a + algebraMap ℚ K (s n)
  have he : ∀ σ : K →ₐ[ℚ] ℂ, Tendsto (fun n => σ (u n)) atTop (𝓝 0) := by
    intro σ
    simpa [u] using (hr.mul_const (σ a)).add hs
  have hp := tendsto_finsetProd Finset.univ (fun σ _ => he σ)
  have hd : Module.finrank ℚ K ≠ 0 := ne_of_gt Module.finrank_pos
  have hn : Tendsto (fun n => ((Algebra.norm ℚ (u n) : ℚ) : ℂ)) atTop (𝓝 0) := by
    simpa [← Algebra.norm_eq_prod_embeddings ℚ ℂ, hd] using hp
  have hnorm := hn.norm
  simp only [norm_zero] at hnorm
  filter_upwards [hnorm.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn
  by_contra h
  exact (not_lt_of_ge (integral_norm_lower_bound (u n) (hi n) h)) hn

lemma real_affine_integral_eventually_zero (a : ℝ) (ha : IsAlgebraic ℚ a)
    (r s : ℕ → ℚ)
    (hr : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0))
    (hs : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 0))
    (hi : ∀ n, IsIntegral ℤ ((r n : ℝ) * a + (s n : ℝ))) :
    ∀ᶠ n in atTop, (r n : ℝ) * a + (s n : ℝ) = 0 := by
  let K := IntermediateField.adjoin ℚ ({a} : Set ℝ)
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional ha.isIntegral
  letI : NumberField K := { to_finiteDimensional := inferInstance }
  let ak : K := ⟨a, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton a)⟩
  have hrC : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hsC : Tendsto (fun n => (s n : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  have hk : ∀ n, IsIntegral ℤ (algebraMap ℚ K (r n) * ak + algebraMap ℚ K (s n)) := by
    intro n
    apply (isIntegral_algebraMap_iff (algebraMap K ℝ).injective).mp
    simpa [ak] using hi n
  filter_upwards [affine_integral_eventually_zero ak r s hrC hsC hk] with n hn
  have hh := congrArg (algebraMap K ℝ) hn
  simpa [ak] using hh

end EulerNormWork


theorem solution (a : ℝ) (ha : IsAlgebraic ℚ a)
    (r s : ℕ → ℚ)
    (hr : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0))
    (hs : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 0))
    (hi : ∀ n, IsIntegral ℤ ((r n : ℝ) * a + (s n : ℝ))) :
    ∀ᶠ n in atTop, (r n : ℝ) * a + (s n : ℝ) = 0 := by
  exact EulerNormWork.real_affine_integral_eventually_zero a ha r s hr hs hi

#print axioms solution
