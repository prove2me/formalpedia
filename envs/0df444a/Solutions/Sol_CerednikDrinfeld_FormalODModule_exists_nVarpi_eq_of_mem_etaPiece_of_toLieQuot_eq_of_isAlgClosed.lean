-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/05c61965-69f7-5fa3-bde3-159970b82632

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierLMapFibre
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq_of_critical_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld

namespace C2Fibre

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.FormalODModule

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] (j : Zp2 p →+* K)
  (X : FormalODModule p K) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))

include hc in
theorem hi_of_isCritical (i : ℕ) (hi : CritChart.IsCritical X j i) :
    ∀ m ∈ X.gradedPiece j i, ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
  intro m hm
  obtain ⟨g, hg⟩ := hi m hm
  exact ⟨g, by rw [verschiebungInt_apply_eq_verschiebung]; exact hg⟩

theorem hsurj_of_isPiBijective (n : Fin 2) (hbij : X.IsPiBijective j (n : ℕ)) :
    ∀ z ∈ X.gradedPiece j ((n + 1 : Fin 2) : ℕ), ∃ m ∈ X.gradedPiece j (n : ℕ),
      ∃ m' : CartierModule p X.F, z = endAct X.varpiEnd m + verschiebungInt m' := by
  intro z hz
  rw [gradedPiece_fin_add_one] at hz
  obtain ⟨f, hf, g, hg⟩ := hbij.2 z hz
  exact ⟨f, hf, g, by rw [verschiebungInt_apply_eq_verschiebung]; exact hg⟩

theorem hinj_of_isPiBijective (n : Fin 2) (hbij : X.IsPiBijective j (n : ℕ)) :
    ∀ m ∈ X.gradedPiece j (n : ℕ),
      (∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m) →
        ∃ g' : CartierModule p X.F, verschiebungInt g' = m := by
  rintro m hm ⟨g, hg⟩
  obtain ⟨g', hg'⟩ := hbij.1 m hm ⟨g, by rw [← verschiebungInt_apply_eq_verschiebung]; exact hg⟩
  exact ⟨g', by rw [verschiebungInt_apply_eq_verschiebung]; exact hg'⟩

end C2Fibre

theorem solution
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p] (j : Zp2 p →+* K)
    (X : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    (∀ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
      (∃ m₁ ∈ X.gradedPiece j 1, (X.toGradedCartierModuleData j hc).toLieQuot z =
          (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₁)) →
      ∃ z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1, (X.toGradedCartierModuleData j hc).nVarpi z₁ = z) ∧
    (∀ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1,
      (∃ m₀ ∈ X.gradedPiece j 0, (X.toGradedCartierModuleData j hc).toLieQuot z =
          (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₀)) →
      ∃ z₀ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0, (X.toGradedCartierModuleData j hc).nVarpi z₀ = z) := by
  classical
  let Φs : SpecialFormalODModule p j := ⟨X, hX, hX4⟩
  obtain ⟨hdich, hcrit01⟩ := CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field p j Φs
  have htors : ∀ m : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.endAct X.varpiEnd m = 0 → m = 0 :=
    fun m hm => CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced p j X hX hX4 m hm
  have hLcrit : ∀ i : ℕ, CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j i →
      ∀ x y : MvFormalGroup.CartierModule p X.F, x ∈ X.gradedPiece j i →
        MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0) :=
    fun i hi x y hx hy => CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL i (C2Fibre.hi_of_isCritical j X hc i hi) x y hx hy
  constructor
  · intro z hz htan
    by_cases h1 : CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 1
    · exact CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one p j X hc L hL (C2Fibre.hi_of_isCritical j X hc 1 h1) (hLcrit 1 h1) z hz htan
    · have hbij1 : X.IsPiBijective j ((1 : Fin 2) : ℕ) := (hdich 1).resolve_left h1
      have h0 : CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 0 := hcrit01.resolve_right h1
      have hEta0 := (CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL htors 0 (C2Fibre.hi_of_isCritical j X hc 0 h0) (hLcrit 0 h0)).1
      have hBij := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP p j X hc L hL 1 (C2Fibre.hsurj_of_isPiBijective j X 1 hbij1) (C2Fibre.hinj_of_isPiBijective j X 1 hbij1)
      refine CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq p j X hc L hL hEta0 ?_ z hz htan
      intro m hm hPV _
      obtain ⟨z₁, hz₁, hlam⟩ := hBij.2.2 ⟨hm, hPV⟩
      exact ⟨z₁, hz₁, hlam⟩
  · intro z hz htan
    by_cases h0 : CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 0
    · exact CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq p j X hc L hL (C2Fibre.hi_of_isCritical j X hc 0 h0) (hLcrit 0 h0) z hz htan
    · have hbij0 : X.IsPiBijective j ((0 : Fin 2) : ℕ) := (hdich 0).resolve_left h0
      have h1 : CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j 1 := hcrit01.resolve_left h0
      have hEta1 := (CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP p j X hc L hL htors 1 (C2Fibre.hi_of_isCritical j X hc 1 h1) (hLcrit 1 h1)).1
      have hBij := CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_charP p j X hc L hL 0 (C2Fibre.hsurj_of_isPiBijective j X 0 hbij0) (C2Fibre.hinj_of_isPiBijective j X 0 hbij0)
      refine CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq_of_critical_one p j X hc L hL hEta1 ?_ z hz htan
      intro m hm hPV _
      obtain ⟨z₀, hz₀, hlam⟩ := hBij.2.2 ⟨hm, hPV⟩
      exact ⟨z₀, hz₀, hlam⟩

end S_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed (solution)
