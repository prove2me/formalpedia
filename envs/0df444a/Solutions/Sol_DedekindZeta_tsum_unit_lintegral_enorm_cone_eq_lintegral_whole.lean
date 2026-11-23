-- Prove2me | solution 1 for DedekindZeta.tsum_unit_lintegral_enorm_cone_eq_lintegral_whole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:50.320373+00:00
-- url     : https://prove2.me/submissions/4be770d3-980a-42e8-905a-6a15f53351d8

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_coneSMul_def
import Theorems.Thm_DedekindZeta_isFundamentalDomain_fundamentalCone
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_norm_unitSMul
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution
    (a : K) (t : ℂ) :
    (∑' g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K
                ((coneUnitHom (K := K) g • y) * mixedEmbedding K a) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      = ∫⁻ x, ‖(Theta.mixedGaussian K (x * mixedEmbedding K a) : ℂ)
          * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by
  -- The cone `MulAction`/measurability/invariance instances are `local` to the
  -- `MulHaarRightInvariance` section above; re-introduce them locally so the
  -- `IsFundamentalDomain.lintegral_eq_tsum''` machinery applies here.
  letI := DedekindZeta.coneMulAction (K := K)
  letI := DedekindZeta.coneMeasurableConstSMul (K := K)
  letI := DedekindZeta.coneCountable (K := K)
  letI := DedekindZeta.coneSMulInvariantMeasure (K := K)
  -- The nonnegative whole-space integrand `f y = ‖g(y·σa)·N(y)^t‖ₑ`.
  set f : mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun y => ‖(Theta.mixedGaussian K (y * mixedEmbedding K a) : ℂ)
      * (mixedEmbedding.norm y : ℂ) ^ t‖ₑ with hf
  have hFD := isFundamentalDomain_fundamentalCone (K := K)
  have hmeas : MeasurableSet (mixedEmbedding.fundamentalCone K) :=
    mixedEmbedding.measurableSet_fundamentalCone K
  -- `∫⁻ f = ∑' g, ∫⁻ x in C, f (g • x)` for the cone fundamental domain.
  rw [hFD.lintegral_eq_tsum'' f]
  refine tsum_congr (fun g => ?_)
  -- Move the cone restriction back into an indicator on the right.
  rw [← MeasureTheory.lintegral_indicator hmeas]
  refine MeasureTheory.lintegral_congr (fun x => ?_)
  by_cases hx : x ∈ mixedEmbedding.fundamentalCone K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hf]
    -- `g • x = coneUnitHom g • x` and the unit action preserves `N`, so
    -- `N (g • x) = N x` and the two integrands coincide.
    simp only [coneSMul_def, Theta.norm_unitSMul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, enorm_zero]
end DedekindZeta
