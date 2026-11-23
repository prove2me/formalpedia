-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedQuadForm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:01.105729+00:00
-- url     : https://prove2.me/submissions/d97b09dd-acfa-4af5-b8e5-1e2634576aa4

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (c : ℝ) (y : mixedSpace K) :
    mixedQuadForm K (c • y) = c ^ 2 * mixedQuadForm K y := by
  unfold mixedQuadForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [normAtPlace_smul, mul_pow, sq_abs]
  ring
end DedekindZeta.ConeRadialReduction
