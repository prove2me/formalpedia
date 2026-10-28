-- Prove2me | solution 1 for FunctionalInequalities.KLS.RegularPotential.poincare_le_of_cumulantBound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:41:56.153239+00:00
-- url     : https://prove2.me/submissions/cdcee8e6-0ac7-4910-b0f5-49a3b4ab0db1

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_BasisChange
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_coordTensor_sq_eq_readable
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_norm_coordTensor_taylorTensor_one_le_of_entries_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorCriterion_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_norm_coordTensor_taylorTensor_sq_le_two_mul_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_interior_support_nonempty_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_integrable_exp_mul_norm_readable
import Theorems.Thm_FunctionalInequalities_KLS_coordTensor_taylorTensor_one_apply_readable

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp
end Moments
end
end
end

section
noncomputable section
open MeasureTheory Set
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_readable hνW hW hconv)
end
end
end

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- **Basis independence of the Hilbert–Schmidt norm.** The Euclidean norm of the coefficient
array of a real multilinear form is the same in any two orthonormal bases. -/
theorem FunctionalInequalities.Analysis.Tensor.norm_coordTensor_eq {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖coordTensor b Φ‖ = ‖coordTensor b' Φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [sum_coordTensor_sq_eq_readable b b' Φ]
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
variable {V : E → ℝ} {a b : ℝ}
theorem FunctionalInequalities.KLS.RegularPotential.logConcave_law (hV : RegularPotential V a b) : LogConcave hV.law := by
  have hW : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact LogConcave.logConcave_of_eq_tilted (ν := hV.law) rfl hW.continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge_readable hW hV.pos.le hV.lower)
theorem FunctionalInequalities.KLS.RegularPotential.interior_support_law (hV : RegularPotential V a b) :
    (interior ((hV.law : ProbabilityMeasure E) : Measure E).support).Nonempty := by
    change
      (interior
        (((volume : Measure E).tilted (-V)).support)).Nonempty
    exact
      FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_readable
        (volume : Measure E) (ν := hV.law) rfl
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff
section
open FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
/-- **BKL Theorem 3.1** (arXiv:2610.05474v1, p. 10, proof p. 17, operator route), the exact
statement `M` of the route file, with `K = taylorCriterionConstant`: for every regular potential
`V` on `ℝⁿ` (BKL (12)) whose law `μ` is centered with `Cov μ ≤ Id`, and every `R ≥ 1` with
`|T_d f| ≤ R^d ‖f‖_{L²(μ)}` for all `f ∈ L²(μ)` and `d ≥ 1` (29) (Hilbert–Schmidt norm in the
standard basis), `C_P(μ) ≤ K R²`.

The law is `volume.tilted (-V)`; (29) passes from functions to `L²` classes (`Lp.memLp`,
`Lp.norm_def`) and from `EuclideanSpace.basisFun` to `stdOrthonormalBasis`
(`norm_coordTensor_eq`), and `taylorCriterion` applies; the centering hypothesis is not used. -/
theorem FunctionalInequalities.KLS.RegularPotential.poincare_le_of_taylor :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
      (hV : KLS.RegularPotential V a b),
      (∫ x, x ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n)))) = 0 →
      (∀ v : EuclideanSpace ℝ (Fin n),
        ∫ x, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2) →
      ∀ R : ℝ, 1 ≤ R →
      (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
        MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n))) → ∀ d : ℕ, 1 ≤ d →
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
            (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f d)‖ ≤
          R ^ d * (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal) →
      Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (K * R ^ 2) := by
  refine ⟨taylorCriterionConstant, by norm_num [taylorCriterionConstant], fun n V a b hV _ hcov R hR h29 => ?_⟩
  have hνU : (hV.law : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-V) := rfl
  refine taylorCriterion_readable volume hV.logConcave_law hV.interior_support_law
    hνU hV.temperate hV.integrable_exp_mul_norm_readable hV.pos hV.lower hcov hR (fun u d hd => ?_)
  rw [norm_coordTensor_eq _ (EuclideanSpace.basisFun (Fin n) ℝ), Lp.norm_def]
  exact h29 u (Lp.memLp u) d hd
end
end
end

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
section
/-- **BKL p. 30, the case `d = 1`**: for an isotropic law on `ℝⁿ` with all exponential moments and
`f ∈ L²(μ)`, `‖T_1 f‖_HS ≤ ‖f‖_{L²(μ)}` (Bessel; assembly of the two previous lemmas). -/
theorem FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : Isotropic μ)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
        (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1)‖ ≤
      (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal :=
  hiso.norm_coordTensor_taylorTensor_one_le_of_entries_readable hf fun i =>
    coordTensor_taylorTensor_one_apply_readable (μ : Measure (EuclideanSpace ℝ (Fin n))) hexp
      hiso.memLp_two hiso.mean_zero hf i
end
/-- `2 K^d ≤ (2K)^d` for `d ≥ 1` and `K ≥ 0` (numeric step of BKL p. 30). -/
theorem FunctionalInequalities.KLS.RegularPotential.two_mul_pow_le_two_mul_pow {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (hd : 1 ≤ d) :
    2 * K ^ d ≤ (2 * K) ^ d := by
    have hpow : (2 : ℝ) ≤ 2 ^ d :=
      le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : d ≠ 0)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hK d)
/-- **BKL p. 30: Theorem 1.1 for regular isotropic laws, conditional on the cumulant bounds of
Theorem 4.1.** If `R^ν_{d+1} ≤ (d!)² K^d · Id` for every isotropic log-concave `ν` in every dimension
and every `d ≥ 2` (`CumulantBound d ((d!)² K^d)`, `K ≥ 1`), then every isotropic regular law on `ℝⁿ`
has literature Poincaré constant at most `2 C K`, where `C` is the constant of Theorem 3.1
(`poincare_le_of_taylor`): Proposition 7.1 gives `|T_d f|² ≤ 2K^d‖f‖² ≤ (2K)^d‖f‖²` for `d ≥ 2`,
isotropy gives `|T_1 f| ≤ ‖f‖`, and Theorem 3.1 applies with `R = √(2K)`. The hypothesis is the
source's Theorem 4.1, discharged in the closed producer `BKL.Localization.exists_isotropicBound`. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      (∀ d : ℕ, 2 ≤ d → FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
      ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : FunctionalInequalities.KLS.RegularPotential V a b),
        FunctionalInequalities.KLS.Isotropic hV.law →
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (2 * C * K) := by
    obtain ⟨C, hC, hT⟩ := FunctionalInequalities.KLS.RegularPotential.poincare_le_of_taylor
    refine ⟨C, hC, fun K hK hcb n V a b hV hiso => ?_⟩
    let E := EuclideanSpace ℝ (Fin n)
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
    let R : ℝ := Real.sqrt (2 * K)
    have hR2 : R ^ 2 = 2 * K := by
      dsimp [R]
      exact Real.sq_sqrt (by positivity)
    have hR1 : 1 ≤ R := by
      have hRnonneg : 0 ≤ R := by
        dsimp [R]
        exact Real.sqrt_nonneg _
      nlinarith [hR2]
    have hmean : (∫ x : E, x ∂(hV.law : Measure E)) = 0 := by
      exact hiso.mean_zero
    have hcov :
        ∀ v : E,
          (∫ x : E, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure E)) ≤ ‖v‖ ^ 2 := by
      intro v
      have hv := hiso.integral_inner_mul_inner v v
      have hv' :
          (∫ x : E, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure E)) = ‖v‖ ^ 2 := by
        simpa [pow_two, real_inner_self_eq_norm_sq] using hv
      exact hv'.le
    have htaylor :
        ∀ f, MemLp f 2 (hV.law : Measure E) →
          ∀ d : ℕ, 1 ≤ d →
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ≤
              R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal := by
      intro f hf d hd
      rcases Nat.lt_or_ge d 2 with hlt | hge
      · have hd1 : d = 1 := by omega
        subst d
        have hone :=
          hiso.norm_coordTensor_taylorTensor_one_le
            hV.integrable_exp_mul_norm_readable hf
        have hE :
            0 ≤ (eLpNorm f 2 (hV.law : Measure E)).toReal :=
          ENNReal.toReal_nonneg
        have hR1' : 1 ≤ R ^ (1 : ℕ) := by
          simpa using hR1
        exact hone.trans (le_mul_of_one_le_left hE hR1')
      · have hparam : 0 < (d.factorial : ℝ) ^ 2 * K ^ d := by
          positivity
        have hsquare :=
          FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_two_mul_readable hge hparam
            (hcb d hge) V hV hiso f hf
        have hfac : (d.factorial : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero d)
        have hcancel :
            2 * ((d.factorial : ℝ) ^ 2 * K ^ d) /
                (d.factorial : ℝ) ^ 2 *
                (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 =
              2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
          field_simp [hfac]
        have hsq :
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2 ≤
              2 * K ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
          calc
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2
                ≤ 2 * ((d.factorial : ℝ) ^ 2 * K ^ d) /
                    (d.factorial : ℝ) ^ 2 *
                    (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := hsquare
            _ = 2 * K ^ d *
                  (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := hcancel
        have hpow : 2 * K ^ d ≤ (2 * K) ^ d :=
          FunctionalInequalities.KLS.RegularPotential.two_mul_pow_le_two_mul_pow (le_of_lt hKpos) hd
        have hsq' :
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2 ≤
              (R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal) ^ 2 := by
          calc
            ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ ^ 2
                ≤ 2 * K ^ d *
                    (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := hsq
            _ ≤ (2 * K) ^ d *
                  (eLpNorm f 2 (hV.law : Measure E)).toReal ^ 2 := by
              exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
            _ = (R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal) ^ 2 := by
              have hp : (2 * K) ^ d = (R ^ d) ^ 2 := by
                calc
                  (2 * K) ^ d = (R ^ 2) ^ d := by rw [hR2]
                  _ = R ^ (2 * d) := by rw [pow_mul]
                  _ = R ^ (d * 2) := by
                    rw [show 2 * d = d * 2 by omega]
                  _ = (R ^ d) ^ 2 := by rw [pow_mul]
              rw [hp]
              ring
        have hnonneg :
            0 ≤ ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
                (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure E) f d)‖ :=
          norm_nonneg _
        have hright :
            0 ≤ R ^ d * (eLpNorm f 2 (hV.law : Measure E)).toReal := by
          exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
        nlinarith
    have hmain := hT n V a b hV hmean hcov R hR1 htaylor
    calc
      FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant hV.law
          ≤ ENNReal.ofReal (C * R ^ 2) := hmain
      _ = ENNReal.ofReal (2 * C * K) := by
        rw [hR2]
        congr 1
        ring
