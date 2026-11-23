-- Prove2me | solution 1 for DedekindZeta.integrable_real_gaussian_mul_abs_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:21:56.148664+00:00
-- url     : https://prove2.me/submissions/f984b35e-fd78-4f27-a356-f40d29a1b71c

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
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
open MeasureTheory NumberField.mixedEmbedding
namespace DedekindZeta
theorem _root_.solution {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (-Real.pi * x ^ 2) * |x| ^ (σ - 1)) := by
  set b : ℝ := Real.pi
  set s : ℝ := σ - 1
  have hb : 0 < b := Real.pi_pos
  have hs : -1 < s := by simp only [s]; linarith
  suffices h : MeasureTheory.Integrable
      (fun x : ℝ => |x| ^ s * Real.exp (-b * x ^ 2)) by
    refine h.congr ?_
    filter_upwards with x
    ring
  have hIoi : MeasureTheory.IntegrableOn
      (fun x : ℝ => |x| ^ s * Real.exp (-b * x ^ 2)) (Set.Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hs).congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
    rw [abs_of_nonneg (le_of_lt hx)]
  rw [← integrableOn_univ, ← @Set.Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hIoi⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, Set.neg_preimage, Set.neg_Iio, neg_zero, abs_neg]
  exact hIoi
end DedekindZeta
