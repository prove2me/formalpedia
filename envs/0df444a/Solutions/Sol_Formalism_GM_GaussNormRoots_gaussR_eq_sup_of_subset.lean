-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.gaussR_eq_sup_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:06.611797+00:00
-- url     : https://prove2.me/submissions/c04a3eba-d99b-4d89-94d5-b466b0defe98

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots
variable {K : Type} [NormedField K]
namespace Formalism.GM.GaussNormRoots
theorem _root_.solution (ρ : NNReal) (P : K[X]) (s : Finset ℕ) (hs : P.support ⊆ s) :
    gaussR ρ P = s.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k) := by
  unfold gaussR
  apply le_antisymm (Finset.sup_mono hs)
  refine Finset.sup_le fun k _ => ?_
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk
  · rw [Polynomial.notMem_support_iff.mp hk]
    simp
end Formalism.GM.GaussNormRoots
