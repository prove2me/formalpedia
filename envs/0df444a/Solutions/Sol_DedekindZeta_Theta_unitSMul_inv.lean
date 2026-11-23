-- Prove2me | solution 1 for DedekindZeta.Theta.unitSMul_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:16:21.121938+00:00
-- url     : https://prove2.me/submissions/a94a44b1-4e67-4d9f-af4b-2a0e47ca028a

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_mixedEmbedding_inv
import Theorems.Thm_DedekindZeta_Theta_mixedSpace_mul_inv
import Theorems.Thm_DedekindZeta_Theta_coe_unit_inv

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (u : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    (u • x)⁻¹ = u⁻¹ • x⁻¹ := by
  rw [unitSMul_smul, unitSMul_smul, mixedSpace_mul_inv, mixedEmbedding_inv]
  have : ((algebraMap (𝓞 K) K) (u : 𝓞 K))⁻¹
      = (algebraMap (𝓞 K) K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
      coe_unit_inv]
  rw [this]
end DedekindZeta.Theta
