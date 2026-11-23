-- Prove2me | solution 1 for DedekindZeta.Theta.coe_unit_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:58.202637+00:00
-- url     : https://prove2.me/submissions/27f3833b-9111-48f2-acc7-85e827e2c49b

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (u : (𝓞 K)ˣ) :
    ((u : 𝓞 K) : K)⁻¹ = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, Units.mul_inv, map_one]
end DedekindZeta.Theta
