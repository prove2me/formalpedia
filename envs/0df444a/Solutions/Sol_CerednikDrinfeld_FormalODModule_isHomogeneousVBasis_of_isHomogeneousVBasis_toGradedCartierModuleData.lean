-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/dae6aa45-f03e-5efa-820d-c1fadbc1e0e9

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt

theorem solution
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] [Algebra ℤ_[p] S] (j : Zp2 p →+* S)
    (X : FormalODModule p S) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → CartierModule p X.F)
    (hγ : (X.toGradedCartierModuleData j hc).IsHomogeneousVBasis γ) :
    X.IsHomogeneousVBasis j γ := by
  classical
  refine ⟨fun i => (FormalODModule.mem_toGradedCartierModuleData_piece_iff X j hc i (γ i)).mp (hγ.1 i), ?_⟩

  have htan : ∀ (c : Fin 2 → S) (y : CartierModule p X.F) (l : Fin 2),
      tangent ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + verschiebungInt y) l =
        ∑ i : Fin 2, c i * tangent (γ i) l := by
    intro c y l
    rw [map_add, tangent_verschiebungInt, add_zero, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [teichmuller_smul, tangent_homothety, Pi.smul_apply, smul_eq_mul]

  have hsurj := MvFormalGroup.CartierModule.tangent_surjective_of_algebra_padicInt p X.F
  have hrow : ∀ k : Fin 2, ∃ c : Fin 2 → S, ∀ l : Fin 2,
      (∑ i : Fin 2, c i * tangent (γ i) l) = if l = k then 1 else 0 := by
    intro k
    obtain ⟨x, hx⟩ := hsurj (fun l => if l = k then 1 else 0)
    obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 x
    refine ⟨c, fun l => ?_⟩
    have h1 : (if l = k then (1 : S) else 0) =
        tangent ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + verschiebungInt y) l :=
      congrFun (hx.symm.trans (congrArg tangent hcy)) l
    rw [h1, htan]
  choose C hC using hrow
  have hCT : (Matrix.of fun k i => C k i) * (Matrix.of fun i l => tangent (γ i) l) = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [hC k l]
    by_cases h : k = l
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  exact Matrix.isUnit_det_of_left_inverse hCT

end S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_of_isHomogeneousVBasis_toGradedCartierModuleData (solution)
