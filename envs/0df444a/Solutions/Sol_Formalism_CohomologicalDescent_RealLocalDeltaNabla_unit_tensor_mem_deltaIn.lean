-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.unit_tensor_mem_deltaIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:30.930317+00:00
-- url     : https://prove2.me/submissions/41ac210f-5fc8-428f-9d60-6c8222e5a059

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (z : ⨂[O] _ : Unit, ↥(deltaIn O r n hn ν)) :
    PiTensorProduct.subsingletonEquiv (R := O) (s := fun _ : Unit => ↥(dualWeyl O r n ν)) ()
      (PiTensorProduct.map (fun _ : Unit => (deltaIn O r n hn ν).subtype) z) ∈
        deltaIn O r n hn ν := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]
    exact Submodule.smul_mem _ c (a ()).2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
