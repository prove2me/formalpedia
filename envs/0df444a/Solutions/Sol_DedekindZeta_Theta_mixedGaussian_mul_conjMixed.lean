-- Prove2me | solution 1 for DedekindZeta.Theta.mixedGaussian_mul_conjMixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:20:25.366578+00:00
-- url     : https://prove2.me/submissions/6c1b9606-cb72-40b6-abc9-819367cbcd3d

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_normAtPlace_conjMixed

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (z ξ : mixedSpace K) :
    mixedGaussian K (z * conjMixed K ξ) = mixedGaussian K (z * ξ) := by
  have hsum : ∀ w : InfinitePlace K,
      (InfinitePlace.mult w : ℝ) * normAtPlace w (z * conjMixed K ξ) ^ 2
        = (InfinitePlace.mult w : ℝ) * normAtPlace w (z * ξ) ^ 2 := by
    intro w
    rw [show normAtPlace w (z * conjMixed K ξ)
          = normAtPlace w z * normAtPlace w (conjMixed K ξ) from map_mul (normAtPlace w) _ _,
        show normAtPlace w (z * ξ) = normAtPlace w z * normAtPlace w ξ from map_mul (normAtPlace w) _ _,
        normAtPlace_conjMixed]
  rw [mixedGaussian, mixedGaussian, Finset.sum_congr rfl (fun w _ => hsum w)]
end DedekindZeta.Theta
