-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8fad79d0-328a-54a8-98cd-8b6132173d25

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_zero_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_of_isHomogeneousVBasis
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_iff_le_ker_lieVarpi_of_isSpecial
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebungInt_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt

noncomputable section

namespace K1aAsm

section Descent
open CerednikDrinfeld.FormalODModule

theorem exists_eq_nsmul_of_mem_invariants_of_tangent_eq_zero
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p]
    (j : Zp2 p →+* κ) (Y : FormalODModule p κ)
    (γ : Fin 2 → CartierModule p Y.F) (hγ : Y.IsHomogeneousVBasis j γ)
    (a : ℕ → Fin 2 → κ) (ha : Y.HasStructureConstants γ a)
    (i₀ : Fin 2) (ha1 : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (m : CartierModule p Y.F) (hm : m ∈ FormalODModule.CritChart.invariants Y j (i₀ : ℕ))
    (htan : tangent m = 0) :
    ∃ m' ∈ FormalODModule.CritChart.invariants Y j (i₀ : ℕ), m = p • m' := by
  classical
  have hsep : IsHausdorff (Ideal.span {(p : κ)}) κ := by
    rw [show Ideal.span {(p : κ)} = ⊥ from Ideal.span_singleton_eq_bot.mpr (CharP.cast_eq_zero κ p)]
    infer_instance
  have hLie : IsCompl (Y.lieZero j) (Y.lieOne j) :=
    (CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis p j hsep Y γ hγ).1
  have hV : ∀ f : CartierModule p Y.F, verschiebungInt f = verschiebung f := fun f =>
    congrFun (congrArg DFunLike.coe (verschiebungInt_eq_verschiebung (p := p) (Φ := Y.F))) f

  have hγne : tangent (γ i₀) ≠ 0 := by
    intro h0
    apply hγ.2.ne_zero
    exact Matrix.det_eq_zero_of_row_eq_zero i₀ (fun k => by rw [Matrix.of_apply, h0, Pi.zero_apply])
  obtain ⟨hm₀, hPm⟩ := hm

  obtain ⟨⟨c, g⟩, ⟨hg, hmexp⟩, -⟩ :=
    CerednikDrinfeld.FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
      p j Y hLie γ hγ (i₀ : ℕ) 1 m hm₀
  have hidx : (⟨((i₀ : ℕ) + 0) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = i₀ :=
    Fin.ext (by simp [Nat.mod_eq_of_lt i₀.isLt])
  simp only [Fin.sum_univ_one, Function.iterate_one, Fin.val_zero, Function.iterate_zero, id] at hmexp
  rw [hidx] at hmexp
  have hc0 : c 0 = 0 := by
    have h := congrArg tangent hmexp
    rw [htan, map_add, tangent_homothety, tangent_verschiebung, add_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hγne
  have hmV : m = verschiebung g := by rw [hmexp, hc0, homothety_zero_left, zero_add]
  have hPg : endAct Y.varpiEnd g = verschiebung g := by
    apply verschiebung_injective
    rw [← endAct_verschiebung, ← hmV, hPm, hmV]

  obtain ⟨⟨d, h⟩, ⟨hh, hgexp⟩, -⟩ :=
    CerednikDrinfeld.FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
      p j Y hLie γ hγ ((i₀ : ℕ) + 1) 1 g hg
  have hidx1 : (⟨((i₀ : ℕ) + 1 + 0) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2) = FormalODModule.piIndex 0 i₀ :=
    Fin.ext (by simp [FormalODModule.piIndex, Nat.add_comm])
  simp only [Fin.sum_univ_one, Function.iterate_one, Fin.val_zero, Function.iterate_zero, id] at hgexp
  rw [hidx1] at hgexp

  obtain ⟨h', hPγ⟩ := ha (FormalODModule.piIndex 0 i₀) 1
  have hidx2 : FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i₀) = i₀ :=
    Fin.ext (by simp [FormalODModule.piIndex]; omega)
  simp only [Fin.sum_univ_one, Function.iterate_one, Fin.val_zero, Function.iterate_zero, id] at hPγ
  rw [hidx2, hV] at hPγ

  have hd0 : d 0 = 0 := by
    have h2 := congrArg tangent hPg
    rw [hgexp] at h2
    simp only [map_add, endAct_homothety, endAct_verschiebung, hPγ, tangent_verschiebung, tangent_homothety,
      add_zero, smul_add, smul_zero, smul_smul] at h2
    have := (smul_eq_zero.mp h2).resolve_right hγne
    exact (mul_eq_zero.mp this).resolve_right ha1
  have hgV : g = verschiebung h := by rw [hgexp, hd0, homothety_zero_left, zero_add]
  have hPh : endAct Y.varpiEnd h = verschiebung h := by
    apply verschiebung_injective
    rw [← endAct_verschiebung, ← hgV, hPg, hgV]
  have hh₀ : h ∈ Y.gradedPiece j (i₀ : ℕ) := by
    rw [← gradedPiece_add_two Y j (i₀ : ℕ)]
    simpa [Nat.add_assoc] using hh
  refine ⟨h, ⟨hh₀, hPh⟩, ?_⟩
  calc m = verschiebung (verschiebung h) := by rw [hmV, hgV]
    _ = verschiebung (endAct Y.varpiEnd h) := by rw [hPh]
    _ = endAct Y.varpiEnd (verschiebung h) := (endAct_verschiebung _ _).symm
    _ = endAct Y.varpiEnd (endAct Y.varpiEnd h) := by rw [hPh]
    _ = p • h := endAct_varpiEnd_endAct_varpiEnd Y h

end Descent

theorem coeff_dvd (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p]
    (j : Zp2 p →+* K) (Y : FormalODModule p K) (i : ℕ)
    (e : Fin 2 → CartierModule p Y.F)
    (he_mem : ∀ r, e r ∈ Y.gradedPiece j i)
    (he_bas : ∀ m ∈ Y.gradedPiece j i, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r)
    (m' : CartierModule p Y.F) (hm' : m' ∈ Y.gradedPiece j i) (c₁ c₂ : ℤ)
    (h : c₁ • e 0 + c₂ • e 1 = p • m') :
    (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂ := by
  classical
  obtain ⟨w, hw, -⟩ := he_bas m' hm'
  have hxM : c₁ • e 0 + c₂ • e 1 ∈ Y.gradedPiece j i :=
    add_mem (zsmul_mem (he_mem 0) c₁) (zsmul_mem (he_mem 1) c₂)
  obtain ⟨u, hu, huniq⟩ := he_bas _ hxM

  have h1 : c₁ • e 0 + c₂ • e 1 = ∑ r, (![(c₁ : WittVector p K), (c₂ : WittVector p K)] r) • e r := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_smul_eq_zsmul]

  have h2 : c₁ • e 0 + c₂ • e 1 = ∑ r, ((p : WittVector p K) * w r) • e r := by
    rw [h, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have key : ∀ r, (![(c₁ : WittVector p K), (c₂ : WittVector p K)] r) = (p : WittVector p K) * w r :=
    fun r => by rw [← e2] at e1; exact congrFun e1 r
  have hp0 : ∀ r, WittVector.constantCoeff (![(c₁ : WittVector p K), (c₂ : WittVector p K)] r) = 0 := by
    intro r
    rw [key r, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  have k0 := hp0 0
  have k1 := hp0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_intCast] at k0 k1
  exact ⟨(CharP.intCast_eq_zero_iff K p c₁).1 k0, (CharP.intCast_eq_zero_iff K p c₂).1 k1⟩

theorem core (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K]
    (j : Zp2 p →+* K) (Y : FormalODModule p K)
    (γ : Fin 2 → CartierModule p Y.F) (hγ : Y.IsHomogeneousVBasis j γ)
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (a : ℕ → Fin 2 → K) (ha : Y.HasStructureConstants γ a)
    (i₀ : Fin 2) (ha0 : a 0 i₀ = 0) (ha1 : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (P P' : Submodule K Y.Lie)
    (hu : ∀ v ∈ P, ∃! b : K, v = b • tangent (γ i₀))
    (hu' : ∀ v ∈ P', ∃! b : K, v = b • tangent (γ (FormalODModule.piIndex 0 i₀)))
    (htan : ∀ f ∈ Y.gradedPiece j (i₀ : ℕ), tangent f ∈ P)
    (htan' : ∀ f ∈ Y.gradedPiece j ((FormalODModule.piIndex 0 i₀ : Fin 2) : ℕ), tangent f ∈ P')
    (hkey : P ≤ LinearMap.ker Y.lieVarpi → FormalODModule.CritChart.IsCritical Y j (i₀ : ℕ))
    (hcard : FormalODModule.CritChart.IsCritical Y j (i₀ : ℕ) → ∀ (c : ℤ_[p] →+* WittVector p K),
      ∃ e : Fin 2 → CartierModule p Y.F,
        (∀ r, e r ∈ FormalODModule.CritChart.invariants Y j (i₀ : ℕ)) ∧
        (∀ m ∈ Y.gradedPiece j (i₀ : ℕ), ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r) ∧
        (∀ z, z ∈ (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ ↔
          ∃ a : Fin 2 → ℤ_[p], z = (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0)) ∧
        (∀ a a' : Fin 2 → ℤ_[p],
          (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a r) • e r, 0) =
            (Y.toGradedCartierModuleData j hc).nMk (∑ r, c (a' r) • e r, 0) → a = a')) :
    ∃ (m₁ m₂ : CartierModule p Y.F) (y₁ y₂ : K),
      (Y.toGradedCartierModuleData j hc).nMk (m₁, 0) ∈
        (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ ∧
      (Y.toGradedCartierModuleData j hc).nMk (m₂, 0) ∈
        (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ ∧
      tangent m₁ = y₁ • tangent (γ i₀) ∧ tangent m₂ = y₂ • tangent (γ i₀) ∧
      ∀ c₁ c₂ : ℤ, c₁ • y₁ + c₂ • y₂ = 0 → (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂ := by
  letI : Algebra ℤ_[p] K := ((ZMod.castHom (dvd_refl p) K).comp (PadicInt.toZMod (p := p))).toAlgebra

  have hPiγ : ∀ i, tangent (endAct Y.varpiEnd (γ i)) = a 0 i • tangent (γ (FormalODModule.piIndex 0 i)) := by
    intro i
    obtain ⟨h, hh⟩ := ha i 1
    rw [hh, Fin.sum_univ_one, map_add]
    simp only [Fin.val_zero, Function.iterate_zero, id_eq, Function.iterate_one]
    rw [tangent_homothety, tangent_verschiebungInt, add_zero]

  have hlie : ∀ f : CartierModule p Y.F, Y.lieVarpi (tangent f) = tangent (endAct Y.varpiEnd f) := by
    intro f
    rw [endAct_apply, tangent_map]
    rfl

  have hcrit : FormalODModule.CritChart.IsCritical Y j (i₀ : ℕ) := by
    apply hkey
    intro v hv
    obtain ⟨b, hb, -⟩ := hu v hv
    rw [LinearMap.mem_ker, hb, map_smul, hlie, hPiγ, ha0, zero_smul, smul_zero]

  let c : ℤ_[p] →+* WittVector p K :=
    (WittVector.map (ZMod.castHom (dvd_refl p) K)).comp (WittVector.equiv p).symm.toRingHom
  obtain ⟨e, he_inv, he_bas, he_eta, he_inj⟩ := hcard hcrit c

  have hmem : ∀ r : Fin 2, (Y.toGradedCartierModuleData j hc).nMk (e r, 0) ∈
      (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ := by
    intro r
    fin_cases r
    · refine (he_eta _).mpr ⟨![1, 0], ?_⟩
      congr 1
      refine Prod.ext ?_ rfl
      show e 0 = ∑ r' : Fin 2, c ((![1, 0] : Fin 2 → ℤ_[p]) r') • e r'
      rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_one, map_zero,
        one_smul, zero_smul, add_zero]
    · refine (he_eta _).mpr ⟨![0, 1], ?_⟩
      congr 1
      refine Prod.ext ?_ rfl
      show e 1 = ∑ r' : Fin 2, c ((![0, 1] : Fin 2 → ℤ_[p]) r') • e r'
      rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_one, map_zero,
        one_smul, zero_smul, zero_add]

  have hcoord : ∀ r : Fin 2, ∃ y : K, tangent (e r) = y • tangent (γ i₀) := by
    intro r
    obtain ⟨y, hy, -⟩ := hu _ (htan _ (he_inv r).1)
    exact ⟨y, hy⟩
  choose y hy using hcoord
  refine ⟨e 0, e 1, y 0, y 1, hmem 0, hmem 1, hy 0, hy 1, ?_⟩

  intro c₁ c₂ hsum
  have hsum' : (c₁ : K) * y 0 + (c₂ : K) * y 1 = 0 := by simpa [zsmul_eq_mul] using hsum
  set f : CartierModule p Y.F := c₁ • e 0 + c₂ • e 1 with hf
  have hfinv : f ∈ FormalODModule.CritChart.invariants Y j (i₀ : ℕ) :=
    add_mem (zsmul_mem (he_inv 0) c₁) (zsmul_mem (he_inv 1) c₂)
  have hftan : tangent f = 0 := by
    rw [hf, map_add, map_zsmul, map_zsmul, hy 0, hy 1, ← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K,
      smul_smul, smul_smul, ← add_smul, hsum', zero_smul]
  obtain ⟨m', hm', hfm'⟩ := exists_eq_nsmul_of_mem_invariants_of_tangent_eq_zero p j Y γ hγ a ha i₀ ha1 f hfinv hftan
  exact coeff_dvd p K j Y (i₀ : ℕ) e (fun r => (he_inv r).1) he_bas m' hm'.1 c₁ c₂ (hf ▸ hfm')

end K1aAsm

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (j : Zp2 p →+* κ) (Y : FormalODModule p κ) (hY4 : Y.HasHeight 4)
    (γ : Fin 2 → CartierModule p Y.F) (hγ : Y.IsHomogeneousVBasis j γ)
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (a : ℕ → Fin 2 → κ) (ha : Y.HasStructureConstants γ a)
    (i₀ : Fin 2) (ha0 : a 0 i₀ = 0) (ha1 : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    ∃ (m₁ m₂ : CartierModule p Y.F) (y₁ y₂ : κ),
      (Y.toGradedCartierModuleData j hc).nMk (m₁, 0) ∈
        (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ ∧
      (Y.toGradedCartierModuleData j hc).nMk (m₂, 0) ∈
        (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ ∧
      tangent m₁ = y₁ • tangent (γ i₀) ∧ tangent m₂ = y₂ • tangent (γ i₀) ∧
      ∀ c₁ c₂ : ℤ, c₁ • y₁ + c₂ • y₂ = 0 → (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂ := by
  have hp0 : (p : κ) = 0 := CharP.cast_eq_zero κ p
  have hsep : IsHausdorff (Ideal.span {(p : κ)}) κ := by
    rw [hp0, Ideal.span_singleton_eq_bot.mpr rfl]
    exact ⟨fun x hx => by simpa [SModEq.bot] using hx 1⟩
  have hYsp : Y.IsSpecial j := CerednikDrinfeld.FormalODModule.isSpecial_of_isHomogeneousVBasis p j hsep Y γ hγ
  have hnil : IsNilpotent (p : κ) := ⟨1, by rw [pow_one, hp0]⟩
  obtain ⟨-, hu0, hu1, -⟩ :=
    CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent p j hnil Y γ hγ
  obtain ⟨ht0, ht1⟩ :=
    CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p j hnil Y
  obtain ⟨hk0, hk1⟩ := CerednikDrinfeld.FormalODModule.CritChart.isCritical_iff_le_ker_lieVarpi_of_isSpecial p j Y hYsp
  fin_cases i₀
  · exact K1aAsm.core p κ j Y γ hγ hc a ha 0 ha0 ha1 L hL (Y.lieZero j) (Y.lieOne j) hu0 hu1 ht0 ht1
      hk0.mpr (fun h c => CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_zero_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
        p κ j Y hYsp hY4 hc L hL h c)
  · exact K1aAsm.core p κ j Y γ hγ hc a ha 1 ha0 ha1 L hL (Y.lieOne j) (Y.lieZero j) hu1 hu0 ht1 ht0
      hk1.mpr (fun h c => CerednikDrinfeld.FormalODModule.exists_forall_mem_etaPiece_one_iff_eq_nMk_sum_smul_of_isCritical_of_isAlgClosed
        p κ j Y hYsp hY4 hc L hL h c)

end
end S_CerednikDrinfeld_FormalODModule_exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed (solution)
