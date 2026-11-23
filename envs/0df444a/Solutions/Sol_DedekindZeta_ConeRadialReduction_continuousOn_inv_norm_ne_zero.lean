-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.continuousOn_inv_norm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:26.130963+00:00
-- url     : https://prove2.me/submissions/3c76cf1d-c952-4eff-bbbc-da4fc972bb3a

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution :
    ContinuousOn (Inv.inv : mixedSpace K → mixedSpace K)
      {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  -- On `{N x ≠ 0}` every coordinate is nonzero (`norm_ne_zero_iff` says every
  -- `normAtPlace w x ≠ 0`, and `normAtPlace` is the coordinate's absolute value).
  have hx' : ∀ w, mixedEmbedding.normAtPlace w x ≠ 0 :=
    mixedEmbedding.norm_ne_zero_iff.mp hx
  have hre : ∀ i : {w : InfinitePlace K // IsReal w}, x.1 i ≠ 0 := by
    intro i
    have h := hx' i.1
    rw [mixedEmbedding.normAtPlace_apply_of_isReal i.2] at h
    simpa using h
  have hco : ∀ i : {w : InfinitePlace K // IsComplex w}, x.2 i ≠ 0 := by
    intro i
    have h := hx' i.1
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex i.2] at h
    simpa using h
  -- Componentwise (Pi) inversion is continuous at a point whose coordinates are
  -- all nonzero, by `continuousAt_inv₀` on ℝ / ℂ at each coordinate.
  have h1 : ContinuousAt (fun p : mixedSpace K => (p.1)⁻¹) x := by
    have hpi : ContinuousAt (Inv.inv : ({w : InfinitePlace K // IsReal w} → ℝ) → _) x.1 := by
      rw [continuousAt_pi]
      intro i
      exact (continuousAt_apply i x.1).inv₀ (hre i)
    exact hpi.comp continuousAt_fst
  have h2 : ContinuousAt (fun p : mixedSpace K => (p.2)⁻¹) x := by
    have hpi : ContinuousAt (Inv.inv : ({w : InfinitePlace K // IsComplex w} → ℂ) → _) x.2 := by
      rw [continuousAt_pi]
      intro i
      exact (continuousAt_apply i x.2).inv₀ (hco i)
    exact hpi.comp continuousAt_snd
  -- `Inv.inv` on the product is `p ↦ (p.1⁻¹, p.2⁻¹)`.
  have hprod : ContinuousAt (fun p : mixedSpace K => ((p.1)⁻¹, (p.2)⁻¹)) x := h1.prodMk h2
  exact hprod
end DedekindZeta.ConeRadialReduction
