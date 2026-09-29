-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.CritChart.isCritical_iff_le_ker_lieVarpi_of_isSpecial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cdb01994-dbee-5896-8925-240bdfabf283

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebung_homothety_add
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

namespace KcCritLie

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [CharP K p]
variable (j : Zp2 p →+* K) (X : FormalODModule p K)

theorem tangent_endAct_varpiEnd (m : CartierModule p X.F) :
    tangent (endAct X.varpiEnd m) = X.lieVarpi (tangent m) := by
  rw [endAct_apply, tangent_map]
  rfl

theorem exists_verschiebung_eq_of_tangent_eq_zero (hX : X.IsSpecial j) (m : CartierModule p X.F)
    (hm : tangent m = 0) : ∃ g : CartierModule p X.F, verschiebung g = m := by
  classical
  obtain ⟨γ, hγ⟩ := exists_isHomogeneousVBasis_of_isSpecial_field p j X hX
  obtain ⟨⟨c, y⟩, hEq, -⟩ :=
    MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebung_homothety_add p X.F γ hγ.2 m 1
  rw [Fin.sum_univ_one] at hEq
  simp only [Fin.val_zero, Function.iterate_zero, id_eq, Function.iterate_one] at hEq

  have ht : tangent m = (Matrix.of fun i k => tangent (γ i) k).vecMul (c 0) := by
    rw [hEq, map_add, tangent_verschiebung, add_zero, map_sum]
    funext k
    rw [Finset.sum_apply]
    show (∑ i, tangent (homothety (c 0 i) (γ i)) k) = ∑ i, c 0 i * tangent (γ i) k
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tangent_homothety, Pi.smul_apply, smul_eq_mul]
  have hc : c 0 = 0 := by
    apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hγ.2)
    show Matrix.vecMul (c 0) (Matrix.of fun i k => tangent (γ i) k) =
      Matrix.vecMul 0 (Matrix.of fun i k => tangent (γ i) k)
    rw [← ht, hm, Matrix.zero_vecMul]
  refine ⟨y, ?_⟩
  rw [hEq, hc]
  simp [homothety_zero_left]

theorem isCritical_iff_aux (hX : X.IsSpecial j) (i : ℕ) (L : Submodule K X.Lie)
    (hL : (X.gradedPiece j i).map tangent = L.toAddSubgroup) :
    CritChart.IsCritical X j i ↔ L ≤ LinearMap.ker X.lieVarpi := by
  constructor
  · intro hi v hv
    have hv' : v ∈ (X.gradedPiece j i).map tangent := by rw [hL]; exact hv
    obtain ⟨m, hm, rfl⟩ := AddSubgroup.mem_map.mp hv'
    obtain ⟨g, hg⟩ := hi m hm
    rw [LinearMap.mem_ker, ← tangent_endAct_varpiEnd, ← hg, tangent_verschiebung]
  · intro hle m hm
    have htm : tangent m ∈ L := by
      have : tangent m ∈ (X.gradedPiece j i).map tangent := AddSubgroup.mem_map.mpr ⟨m, hm, rfl⟩
      rw [hL] at this; exact this
    have h0 : tangent (endAct X.varpiEnd m) = 0 := by
      rw [tangent_endAct_varpiEnd]; exact hle htm
    exact exists_verschiebung_eq_of_tangent_eq_zero j X hX _ h0

theorem main (hX : X.IsSpecial j) :
    (CritChart.IsCritical X j 0 ↔ X.lieZero j ≤ LinearMap.ker X.lieVarpi) ∧
    (CritChart.IsCritical X j 1 ↔ X.lieOne j ≤ LinearMap.ker X.lieVarpi) := by
  have hgr := isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j X hX.1
  exact ⟨isCritical_iff_aux j X hX 0 _ hgr.2.2.2.2.2.2.1,
    isCritical_iff_aux j X hX 1 _ hgr.2.2.2.2.2.2.2⟩

end KcCritLie

theorem solution
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [CharP K p]
    (j : CerednikDrinfeld.Zp2 p →+* K) (X : CerednikDrinfeld.FormalODModule p K)
    (hX : X.IsSpecial j) :
    (CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 0 ↔
        X.lieZero j ≤ LinearMap.ker X.lieVarpi) ∧
    (CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 1 ↔
        X.lieOne j ≤ LinearMap.ker X.lieVarpi) :=
  KcCritLie.main j X hX

end S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial (solution)
