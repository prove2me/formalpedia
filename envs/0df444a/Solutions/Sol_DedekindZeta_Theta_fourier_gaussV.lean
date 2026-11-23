-- Prove2me | solution 1 for DedekindZeta.Theta.fourier_gaussV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:14:20.135752+00:00
-- url     : https://prove2.me/submissions/3f89d00a-7534-4061-854f-7f4acc742e1c

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
theorem _root_.solution (w : minkowskiSpace K) : 𝓕 (gaussV K) w = gaussV K w := by
  unfold gaussV
  rw [fourier_gaussian_innerProductSpace (b := (Real.pi : ℂ)) (by simp [Real.pi_pos])]
  rw [div_self (by exact_mod_cast Real.pi_ne_zero), Complex.one_cpow, one_mul]
  congr 1
  field_simp
end DedekindZeta.Theta
