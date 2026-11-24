-- Prove2me | solution 1 for Formalism.GM.FockB.atoms_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:25.039016+00:00
-- url     : https://prove2.me/submissions/33a146f0-96bd-4bf0-9934-3e3982025590

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.FockB
theorem _root_.solution {S S' : Set σ} (hS : Disjoint S S') {T T' : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ atoms S) (hT' : T' ∈ atoms S') : Commute T T' := by
  obtain ⟨u, hu, hTu⟩ := hT
  obtain ⟨v, hv, hTv⟩ := hT'
  have huv : u ≠ v := fun h => Set.disjoint_left.mp hS hu (h ▸ hv)
  rw [commute_iff_eq]
  refine LinearMap.ext fun f => ?_
  rcases hTu with rfl | rfl <;> rcases hTv with rfl | rfl <;>
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  · ring
  · rw [pderiv_mul, pderiv_X_of_ne huv]; ring
  · rw [pderiv_mul, pderiv_X_of_ne (Ne.symm huv)]; ring
  · exact ProjS.pderiv_comm _ _ _
end Formalism.GM.FockB
