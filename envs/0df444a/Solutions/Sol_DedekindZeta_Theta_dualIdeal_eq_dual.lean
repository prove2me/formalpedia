-- Prove2me | solution 1 for DedekindZeta.Theta.dualIdeal_eq_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:07:55.096814+00:00
-- url     : https://prove2.me/submissions/bf42611b-a11f-4541-a2d1-328ff3007b12

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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) :
    FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = dualIdeal K 𝔞 := by
  have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentFractionalIdeal K)⁻¹ := by
    have h := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
    rw [differentFractionalIdeal, h, inv_inv]
  rw [FractionalIdeal.dual_eq_mul_inv, hd1, dualIdeal, mul_inv, mul_comm]
end DedekindZeta.Theta
