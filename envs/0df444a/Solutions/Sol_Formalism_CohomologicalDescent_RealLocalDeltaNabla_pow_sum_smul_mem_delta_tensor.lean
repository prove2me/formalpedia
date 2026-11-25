-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.pow_sum_smul_mem_delta_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:26.734909+00:00
-- url     : https://prove2.me/submissions/ffb6daee-bfcd-4d91-9055-f655a5169e53

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_latIncl_deltaIn_of_int
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
variable (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ) (hl : l.Prime)
  (hlO : ¬ IsUnit (l : O)) (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
  (ν : ∀ i, Fin (n i) → ℕ) (e : ι → ℕ) (he : ∀ i, InclZ (r i) (n i) (hn i) (ν i) l (e i))
include hl hlO he
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution (y : Nabla O r n ν) : (l : O) ^ (∑ i, e i) • y ∈ Delta O r n hn ν := by
  unfold Delta tensSub
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c a =>
    have hmem : ∀ i, (l : O) ^ e i • a i ∈ deltaIn O (r i) (n i) (hn i) (ν i) := fun i =>
      latIncl_deltaIn_of_int O l hl hlO ι r n hn ν e he i (a i)
    have key : (l : O) ^ (∑ i, e i) • PiTensorProduct.tprod O a =
        PiTensorProduct.map (fun i => (deltaIn O (r i) (n i) (hn i) (ν i)).subtype)
          (PiTensorProduct.tprod O (fun i =>
            (⟨(l : O) ^ e i • a i, hmem i⟩ : deltaIn O (r i) (n i) (hn i) (ν i)))) := by
      rw [PiTensorProduct.map_tprod]
      simp only [Submodule.coe_subtype]
      rw [MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
    rw [smul_comm ((l : O) ^ (∑ i, e i)) c, key]
    exact Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)
  | add x y hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
