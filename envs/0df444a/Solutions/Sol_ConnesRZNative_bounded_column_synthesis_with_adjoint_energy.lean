-- Prove2me | solution 1 for ConnesRZNative.bounded_column_synthesis_with_adjoint_energy
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T23:22:02.142846+00:00
-- url     : https://prove2.me/submissions/3c0a297c-3785-4483-b6da-143718056881

import Mathlib
open scoped BigOperators InnerProductSpace lp ENNReal Classical
set_option autoImplicit false
noncomputable section
namespace WeilDefect.ConnesNative

variable {ι H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Auxiliary norm sequence for a supplied column family. This records a
summability proof; it does not change the columns or the physical carrier. -/
def columnNormCoefficients (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2)) : ℓ²(ι, ℂ) :=
  ⟨fun i => (‖v i‖ : ℂ), memℓp_gen (by
    simpa [Complex.norm_real, Real.norm_eq_abs, Real.rpow_natCast] using hv)⟩

lemma columnSeries_norm_summable (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) : Summable (fun i => ‖u i • v i‖) := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have hh := (lp.tsum_mul_le_mul_norm hp u (columnNormCoefficients v hv)).1
  simpa [norm_smul, columnNormCoefficients, Complex.norm_real, Real.norm_eq_abs] using hh

lemma columnSeries_summable (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) : Summable (fun i => u i • v i) :=
  (columnSeries_norm_summable v hv u).of_norm

lemma columnSeries_bound (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) :
    ‖∑' i, u i • v i‖ ≤ ‖columnNormCoefficients v hv‖ * ‖u‖ := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have hh := lp.tsum_mul_le_mul_norm hp u (columnNormCoefficients v hv)
  calc
    _ ≤ ∑' i, ‖u i • v i‖ := norm_tsum_le_tsum_norm (columnSeries_norm_summable v hv u)
    _ = ∑' i, ‖u i‖ * ‖columnNormCoefficients v hv i‖ := by
      simp [norm_smul, columnNormCoefficients, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖u‖ * ‖columnNormCoefficients v hv‖ := hh.2
    _ = _ := mul_comm _ _

/-- Bounded synthesis of EXACTLY the supplied columns, with the ordinary l2
coefficient carrier. This is the extension of their finite linear combinations,
not a replacement for a native metric or a postulated bounded operator. -/
def columnSynthesis (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ℓ²(ι, ℂ) →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun u => ∑' i, u i • v i
      map_add' := fun u w => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (columnSeries_summable v hv u).tsum_add (columnSeries_summable v hv w)
      map_smul' := fun c u => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_smul]
        simpa only [smul_smul, smul_eq_mul, RingHom.id_apply] using
          (columnSeries_summable v hv u).tsum_const_smul c }
    ‖columnNormCoefficients v hv‖ (columnSeries_bound v hv)

theorem columnSynthesis_apply (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) : columnSynthesis v hv u = ∑' i, u i • v i := rfl

theorem columnNormCoefficients_norm_sq (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ‖columnNormCoefficients v hv‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (columnNormCoefficients v hv)
  simpa [columnNormCoefficients, Real.rpow_two, Complex.norm_real] using hh

theorem columnSynthesis_norm_sq_le (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ‖columnSynthesis v hv‖ ^ 2 ≤ ∑' i, ‖v i‖ ^ 2 := by
  have hb : ‖columnSynthesis v hv‖ ≤ ‖columnNormCoefficients v hv‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    exact columnSeries_bound v hv
  rw [← columnNormCoefficients_norm_sq v hv]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

theorem columnSynthesis_single (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (i : ι) (c : ℂ) : columnSynthesis v hv (lp.single 2 i c) = c • v i := by
  classical
  rw [columnSynthesis_apply]
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

/-- The adjoint coordinates are the inner products with the ORIGINAL columns. -/
theorem columnSynthesis_adjoint_coordinate (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) (h : H) (i : ι) :
    (ContinuousLinearMap.adjoint (columnSynthesis v hv)) h i = ⟪v i, h⟫_ℂ := by
  have hh := ContinuousLinearMap.adjoint_inner_right (columnSynthesis v hv)
    (lp.single 2 i (1 : ℂ)) h
  rw [columnSynthesis_single, one_smul] at hh
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hh

/-- Parseval for the constructed adjoint: the exact column norm identity is
proved, not supplied as an arithmetic attachment premise. -/
theorem columnSynthesis_adjoint_norm_sq (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) (h : H) :
    ‖(ContinuousLinearMap.adjoint (columnSynthesis v hv)) h‖ ^ 2 =
      ∑' i, ‖⟪v i, h⟫_ℂ‖ ^ 2 := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    ((ContinuousLinearMap.adjoint (columnSynthesis v hv)) h)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    columnSynthesis_adjoint_coordinate] using hh

/-- Custody/uniqueness: a supplied native synthesis with the same columns is
the constructed extension. No freedom to change the physical operator remains. -/
theorem columnSynthesis_unique [DecidableEq ι] (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (S : ℓ²(ι, ℂ) →L[ℂ] H)
    (hcolumns : ∀ i, S (lp.single 2 i (1 : ℂ)) = v i) : S = columnSynthesis v hv := by
  ext u
  have hs := S.hasSum (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) u)
  have heq : (fun i => S (lp.single 2 i (u i))) = fun i => u i • v i := by
    funext i
    have hh : lp.single (E := fun _ : ι => ℂ) 2 i (u i) =
        u i • lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ι => ℂ) 2 i (u i) (1 : ℂ))
    rw [hh, map_smul, hcolumns]
  rw [heq] at hs
  exact hs.tsum_eq.symm

end WeilDefect.ConnesNative

open WeilDefect.ConnesNative
theorem solution {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ∃ S : ℓ²(ι, ℂ) →L[ℂ] H,
      (∀ u, S u = ∑' i, u i • v i) ∧
      (∀ i, S (lp.single 2 i (1 : ℂ)) = v i) ∧
      (∀ h i, (ContinuousLinearMap.adjoint S) h i = ⟪v i, h⟫_ℂ) ∧
      (∀ h, ‖(ContinuousLinearMap.adjoint S) h‖ ^ 2 = ∑' i, ‖⟪v i, h⟫_ℂ‖ ^ 2) ∧
      ‖S‖ ^ 2 ≤ ∑' i, ‖v i‖ ^ 2 ∧
      (∀ T : ℓ²(ι, ℂ) →L[ℂ] H,
        (∀ i, T (lp.single 2 i (1 : ℂ)) = v i) → T = S) := by
  refine ⟨columnSynthesis v hv, columnSynthesis_apply v hv, ?_,
    columnSynthesis_adjoint_coordinate v hv, columnSynthesis_adjoint_norm_sq v hv,
    columnSynthesis_norm_sq_le v hv, ?_⟩
  · intro i
    simpa only [one_smul] using columnSynthesis_single v hv i (1 : ℂ)
  · intro T hT
    exact columnSynthesis_unique v hv T hT

#print axioms solution
