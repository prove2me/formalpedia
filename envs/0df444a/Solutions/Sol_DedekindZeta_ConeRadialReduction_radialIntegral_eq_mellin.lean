-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.radialIntegral_eq_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:33:26.288242+00:00
-- url     : https://prove2.me/submissions/4b2b34a8-4476-4f68-997f-5282e478f8ec

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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    ∫ r in Set.Ioi (0 : ℝ),
        orbitTheta K 𝔞 r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume
      = mellin (orbitTheta K 𝔞) s := by
  rw [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rw [smul_eq_mul, Complex.ofReal_inv, Complex.cpow_sub _ _ hrne, Complex.cpow_one]
  field_simp
end DedekindZeta.ConeRadialReduction
