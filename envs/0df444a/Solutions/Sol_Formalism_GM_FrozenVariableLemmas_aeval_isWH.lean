-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.aeval_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:42.461265+00:00
-- url     : https://prove2.me/submissions/52dbb7ed-7993-4e06-8823-8695e47a6a4c

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution {σ τ R : Type} [CommSemiring R] (w' : σ → ℕ) (w : τ → ℕ)
    (g : σ → MvPolynomial τ R) (hg : ∀ x, IsWeightedHomogeneous w (g x) (w' x))
    {f : MvPolynomial σ R} {d : ℕ} (hf : IsWeightedHomogeneous w' f d) :
    IsWeightedHomogeneous w (aeval g f) d := by
  rw [aeval_def, eval₂_eq]
  refine IsWeightedHomogeneous.sum _ _ _ (fun m hm => ?_)
  have hdeg : Finsupp.weight w' m = d := hf (mem_support_iff.mp hm)
  have hprod : IsWeightedHomogeneous w (∏ i ∈ m.support, g i ^ m i) (∑ i ∈ m.support, m i • w' i) :=
    IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hg i).pow (m i))
  have hC := (isWeightedHomogeneous_C w (coeff m f)).mul hprod
  rw [zero_add] at hC
  rw [← hdeg, Finsupp.weight_apply]
  exact hC
end Formalism.GM.FrozenVariableLemmas
