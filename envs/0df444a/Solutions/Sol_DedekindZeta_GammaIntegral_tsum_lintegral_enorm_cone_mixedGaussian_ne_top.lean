-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.tsum_lintegral_enorm_cone_mixedGaussian_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:07.466922+00:00
-- url     : https://prove2.me/submissions/722e2aad-daec-4ec9-b421-88feae17c90b

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_measurable_mixedGaussian_comp_mul_norm_cpow
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_eq_mixed
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_summable_mixedGaussian_submodule
import Theorems.Thm_DedekindZeta_integrable_indicator_mixedThetaKernel_mul_norm_cpow
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) (hs : 1 < s.re)
    {a : Ideal (RingOfIntegers K)} (ha : a ≠ 0) :
    (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun x => (mixedGaussian K
                (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ ∂(mixedMulHaar K))
      ≠ ∞ := by
  classical
  set C := mixedEmbedding.fundamentalCone K with hC
  set μ := mixedMulHaar K with hμ
  -- `s ≠ 0` (from `1 < Re s`), so `(0 : ℂ) ^ s = 0`.
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  -- Helper: the `enorm` of a nonnegative real, embedded in `ℂ`.
  have enorm_ofReal_nonneg : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
    intro r hr
    calc ‖(r : ℂ)‖ₑ = ENNReal.ofReal ‖(r : ℂ)‖ := (ofReal_norm _).symm
      _ = ENNReal.ofReal r := by rw [Complex.norm_real, Real.norm_of_nonneg hr]
  -- The per-element nonnegative integrand whose `tsum` of `lintegral`s we bound.
  set f : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0}
      → mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun a' x => ‖C.indicator (fun x => (mixedGaussian K
          (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ with hf
  -- Each `f a'` is measurable (enorm of a Borel indicator of a Borel function).
  haveI : Countable (RingOfIntegers K) := by
    let b := Module.Free.chooseBasis ℤ (RingOfIntegers K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  have hmeas : ∀ a', AEMeasurable (f a') μ := by
    intro a'
    exact (((measurable_mixedGaussian_comp_mul_norm_cpow s
      (mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))).indicator
      (measurableSet_fundamentalCone K)).enorm).aemeasurable
  -- Tonelli: pull the `tsum` (nonnegative summands) inside the `lintegral`.
  rw [← lintegral_tsum hmeas]
  -- Pointwise, the element-wise `tsum` of `enorm`s is the `enorm` of the cone
  -- indicator of `idealThetaKernel K a · |N x|^s`.
  set I : FractionalIdeal (RingOfIntegers K)⁰ K :=
    (a : FractionalIdeal (RingOfIntegers K)⁰ K) with hI
  have hIne : I ≠ 0 := by
    rw [hI]; exact (FractionalIdeal.coeIdeal_ne_zero).mpr ha
  -- Membership of integral elements in the coerced fractional ideal.
  have hmem : ∀ a' : RingOfIntegers K, a' ∈ a →
      ((a' : RingOfIntegers K) : K) ∈ (I : Submodule (RingOfIntegers K) K) := by
    intro a' ha'
    rw [FractionalIdeal.mem_coe, hI, RingOfIntegers.coe_eq_algebraMap]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ ha'
  have hpt : (fun x => ∑' a', f a' x)
      = (fun x => ‖C.indicator (fun x => Theta.idealThetaKernel K a x
            * (mixedEmbedding.norm x : ℂ) ^ s) x‖ₑ) := by
    funext x
    by_cases hx : x ∈ C
    · -- On the cone the indicators are transparent.
      have hfx : ∀ a', f a' x = ‖(mixedGaussian K
            (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ s‖ₑ := by
        intro a'; rw [hf]; simp only [Set.indicator_of_mem hx]
      simp only [hfx, enorm_mul, ENNReal.tsum_mul_right, Set.indicator_of_mem hx, enorm_mul]
      -- It remains to compare the bracketed factors.
      by_cases hN : mixedEmbedding.norm x = 0
      · -- `|N x| = 0` kills the common norm-power factor.
        have : ‖(mixedEmbedding.norm x : ℂ) ^ s‖ₑ = 0 := by
          rw [hN]; simp [Complex.zero_cpow hs0]
        rw [this, mul_zero, mul_zero]
      · -- `|N x| ≠ 0`: the Gaussian lattice sum is summable, so the two brackets agree.
        have hsumC : Summable (fun b : (I : Submodule (RingOfIntegers K) K) =>
            (mixedGaussian K (x * mixedEmbedding K (b : K)) : ℂ)) :=
          summable_mixedGaussian_submodule K I hIne hN
        have hsumR : Summable (fun b : (I : Submodule (RingOfIntegers K) K) =>
            mixedGaussian K (x * mixedEmbedding K (b : K))) :=
          Complex.summable_ofReal.mp hsumC
        -- Inject the index `{a' ∈ a, a' ≠ 0}` into the fractional-ideal lattice.
        let ι : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0}
            → (I : Submodule (RingOfIntegers K) K) :=
          fun a' => ⟨((a'.1 : RingOfIntegers K) : K), hmem a'.1 a'.2.1⟩
        have hι : Function.Injective ι := by
          intro a₁ a₂ h
          apply Subtype.ext
          apply RingOfIntegers.coe_injective
          exact congrArg (fun t : (I : Submodule (RingOfIntegers K) K) => (t : K)) h
        have hsumS : Summable (fun a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0} =>
            mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))) :=
          (hsumR.comp_injective hι).congr (fun a' => rfl)
        have hnn : ∀ a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
            0 ≤ mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) :=
          fun a' => (Real.exp_pos _).le
        -- LHS bracket.
        have hL : (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
              ‖(mixedGaussian K
                  (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K)) : ℂ)‖ₑ)
            = ENNReal.ofReal (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
                mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))) := by
          rw [ENNReal.ofReal_tsum_of_nonneg hnn hsumS]
          exact tsum_congr (fun a' => enorm_ofReal_nonneg _ (hnn a'))
        -- RHS bracket.
        have hR : ‖Theta.idealThetaKernel K a x‖ₑ
            = ENNReal.ofReal (∑' a' : {a' : RingOfIntegers K // a' ∈ a ∧ a' ≠ 0},
                mixedGaussian K (x * mixedEmbedding K ((a'.1 : RingOfIntegers K) : K))) := by
          rw [Theta.idealThetaKernel, ← Complex.ofReal_tsum,
            enorm_ofReal_nonneg _ (tsum_nonneg hnn)]
        rw [hL, hR]
    · -- Off the cone every indicator vanishes.
      have hfx : ∀ a', f a' x = 0 := by
        intro a'; rw [hf]; simp only [Set.indicator_of_notMem hx, enorm_zero]
      simp only [hfx, tsum_zero, Set.indicator_of_notMem hx, enorm_zero]
  rw [hpt]
  -- Identify `idealThetaKernel` with `mixedThetaKernel` of the coerced ideal and
  -- conclude finiteness from `integrable_indicator_mixedThetaKernel_mul_norm_cpow`.
  simp only [Theta.idealThetaKernel_eq_mixed, ← hI]
  have hint := integrable_indicator_mixedThetaKernel_mul_norm_cpow K I s hs
  exact (hint.hasFiniteIntegral).ne
end DedekindZeta.GammaIntegral
