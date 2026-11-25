-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.pow_smul_weighted_component_mem_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:00.531365+00:00
-- url     : https://prove2.me/submissions/9566b1ab-f753-4a98-836f-02220cdd6657

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_DepthNonnegative_isUnit_intCast_of_not_dvd__e87bbe229176
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_map_smul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_map_weyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_bidet_rowHom
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ)
    (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) (hE : ExpLe l r ν μ e)
    (x : MvPolynomial (Fin r × Fin r) R) (hx : x ∈ dualWeyl R r r ν) :
    (l : R) ^ e • weightedHomogeneousComponent (rowW r r) μ x ∈ weyl R r r le_rfl ν := by
  classical
  rw [standardMonomialSpanDomain R r r ν] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hg
    have hhom := ldbasis_bidet_rowHom R sz hsz I
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hhom)]
    split_ifs with hw
    · have h1 : bideterminant ℤ sz hsz I ∈ nablaWt r ν μ := by
        refine Submodule.mem_inf.2 ⟨hshape ▸ bidetMem ℤ r r K sz hsz I, ?_⟩
        rw [hw]
        exact (mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_bidet_rowHom ℤ sz hsz I)
      obtain ⟨m, hm, h2⟩ := hE _ h1
      have h3 := LA.la_map_weyl R le_rfl ν _ h2
      rw [LA.la_map_smul, ldlat_map_bidet] at h3
      obtain ⟨u, hu'⟩ := isUnit_intCast_of_not_dvd' R l hu m hm
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : R) h3
      rw [smul_smul] at h4
      convert h4 using 2
      push_cast
      rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [smul_zero]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ _ hx
end Formalism.CohomologicalDescent.DepthNonnegative
