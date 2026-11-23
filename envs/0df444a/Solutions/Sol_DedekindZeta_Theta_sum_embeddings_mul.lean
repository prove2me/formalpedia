-- Prove2me | solution 1 for DedekindZeta.Theta.sum_embeddings_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:09:18.691397+00:00
-- url     : https://prove2.me/submissions/bd5170db-2de0-4d77-9d10-78df0d63c053

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
theorem _root_.solution (b a : K) :
    (∑ σ : K →+* ℂ, σ b * σ a) = algebraMap ℚ ℂ (Algebra.trace ℚ K (b * a)) := by
  have hmul : ∀ σ : K →+* ℂ, σ b * σ a = σ (b * a) := fun σ => (map_mul σ b a).symm
  simp_rw [hmul]
  rw [trace_eq_sum_embeddings (E := ℂ)]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ : K →+* ℂ => σ (b * a))
    (fun φ : K →ₐ[ℚ] ℂ => φ (b * a)) (fun σ => rfl)
end DedekindZeta.Theta
