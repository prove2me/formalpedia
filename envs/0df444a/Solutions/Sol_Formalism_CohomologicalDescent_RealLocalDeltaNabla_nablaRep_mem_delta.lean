-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep_mem_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:54.951656+00:00
-- url     : https://prove2.me/submissions/354ad5b6-1416-4768-88b9-1471d3c4a6da

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_nabla_rep_tensor_product
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_delta_lattice_stable_holds

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
theorem _root_.solution (O : Type) [CommRing O] (ι : Type) (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ) (g : ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O)
    (x : Nabla O r n ν) (hx : x ∈ Delta O r n hn ν) : nablaRep O r n ν g x ∈ Delta O r n hn ν := by
  unfold Delta tensSub at hx ⊢
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
  clear hx
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    rw [map_smul, map_smul, PiTensorProduct.map_tprod, (nabla_rep_tensor_product O ι r n ν g _).1]
    refine Submodule.smul_mem _ c (LinearMap.mem_range.mpr ⟨PiTensorProduct.tprod O (fun i =>
      (⟨dualWeylRep O (r i) (n i) (ν i) (g i) (a i),
        delta_lattice_stable_holds O (r i) (n i) (hn i) (ν i) (g i) _ (a i).2⟩ :
          deltaIn O (r i) (n i) (hn i) (ν i))), ?_⟩)
    rw [PiTensorProduct.map_tprod]
    all_goals rfl
  | add x y ihx ihy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ihx ihy
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
