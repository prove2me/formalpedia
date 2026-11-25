-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.tensor_injective_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:18:56.855748+00:00
-- url     : https://prove2.me/submissions/463ba34a-070f-4ed6-924d-a04752d698c1

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_latIncl_deltaIn_of_int
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_delta_lattice_free
import Theorems.Thm_Formalism_CohomologicalDescent_LA_exact_z_specialization


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
theorem _root_.solution : TensorInj := by
  intro O _ _ _ _ l hl hlO ι _ r n hn ν hν
  classical
  have hfree : ∀ i, Module.Free O (deltaIn O (r i) (n i) (hn i) (ν i)) :=
    fun i => delta_lattice_free O (r i) (n i) (hn i) (ν i) (hν i)
  have hF : Module.Free O (⨂[O] i, ↥(deltaIn O (r i) (n i) (hn i) (ν i))) :=
    Module.Free.of_basis (Basis.piTensorProduct fun i =>
      Module.Free.chooseBasis O (deltaIn O (r i) (n i) (hn i) (ν i)))
  have hlat : ∀ i, LatIncl (l : O) (deltaIn O (r i) (n i) (hn i) (ν i))
      (exZ (r i) (n i) (hn i) (ν i) l) :=
    latIncl_deltaIn_of_int O l hl hlO ι r n hn ν _
      (fun i => exact_z_specialization (r i) (n i) (hn i) (ν i) (hν i) l hl)
  let ψ : ∀ i, ↥(dualWeyl O (r i) (n i) (ν i)) →ₗ[O] ↥(deltaIn O (r i) (n i) (hn i) (ν i)) :=
    fun i => LinearMap.codRestrict _
      ((l : O) ^ exZ (r i) (n i) (hn i) (ν i) l • LinearMap.id) (fun c => hlat i c)
  have key : ∀ z : ⨂[O] i, ↥(deltaIn O (r i) (n i) (hn i) (ν i)),
      PiTensorProduct.map ψ
        (PiTensorProduct.map (fun i => (deltaIn O (r i) (n i) (hn i) (ν i)).subtype) z) =
      (l : O) ^ exSum r n hn ν l • z := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod c a =>
      rw [map_smul, map_smul, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, smul_comm]
      congr 1
      have h2 : (fun i => ψ i ((deltaIn O (r i) (n i) (hn i) (ν i)).subtype (a i))) =
          fun i => (l : O) ^ exZ (r i) (n i) (hn i) (ν i) l • a i := by
        funext i
        apply Subtype.ext
        rfl
      rw [h2, MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h3 := key z
  rw [hz, map_zero] at h3
  have hl0 : (l : O) ^ exSum r n hn ν l ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  exact (smul_eq_zero.1 h3.symm).resolve_left hl0
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
