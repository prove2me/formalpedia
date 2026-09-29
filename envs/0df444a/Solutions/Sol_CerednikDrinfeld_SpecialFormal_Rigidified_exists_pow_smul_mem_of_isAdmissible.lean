-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_mem_of_isAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/739b071f-63ca-556d-be75-4c8984eb1389

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_mem_of_isAdmissible
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace GlobalMultipleKit

theorem isHausdorff_of_isNilpotent {p : ℕ} {S : Type} [CommRing S] (hS : IsNilpotent ((p : ℕ) : S)) :
    IsHausdorff (Ideal.span {((p : ℕ) : S)}) S := by
  obtain ⟨N, hN⟩ := hS
  refine ⟨fun x hx => ?_⟩
  have := hx N
  rwa [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Submodule.bot_smul, SModEq.bot] at this

theorem exists_pow_mul_eq_coe (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    ∃ (n : ℕ) (a : ℤ_[p]), (p : ℚ_[p]) ^ n * x = (a : ℚ_[p]) := by
  by_cases hx : x = 0
  · exact ⟨0, 0, by simp [hx]⟩
  refine ⟨(-x.valuation).toNat, ⟨(p : ℚ_[p]) ^ (-x.valuation).toNat * x, ?_⟩, rfl⟩
  rw [Padic.norm_le_one_iff_val_nonneg]
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Padic.valuation_mul (pow_ne_zero _ hp) hx, Padic.valuation_pow, Padic.valuation_p, mul_one]
  have := Int.self_le_toNat (-x.valuation)
  omega

theorem exists_pow_smul_eq_coe (p : ℕ) [Fact p.Prime] (v : Fin 2 → ℚ_[p]) :
    ∃ (m : ℕ) (w : Fin 2 → ℤ_[p]), (p : ℚ_[p]) ^ m • v = fun j => ((w j : ℤ_[p]) : ℚ_[p]) := by
  obtain ⟨n₀, a₀, h₀⟩ := exists_pow_mul_eq_coe p (v 0)
  obtain ⟨n₁, a₁, h₁⟩ := exists_pow_mul_eq_coe p (v 1)
  refine ⟨n₀ + n₁, ![(p : ℤ_[p]) ^ n₁ * a₀, (p : ℤ_[p]) ^ n₀ * a₁], ?_⟩
  funext j
  fin_cases j
  · simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Matrix.cons_val_zero]
    push_cast
    rw [← h₀]; ring
  · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    rw [← h₁]; ring

end GlobalMultipleKit

open GlobalMultipleKit

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) (N : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)
    (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) :
    ∃ c : ℕ, (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ c • v ∈ N x := by
  classical

  obtain ⟨f, hf, γ, hγ⟩ := CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_map_of_isSpecial_of_isNilpotent
    p (structureMap ι ψ) hB t.X ht.1 x
  have hp0 : IsNilpotent ((p : ℕ) : Rigidified.Baway f) := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, by rw [← map_natCast (Rigidified.awayHom f) p, ← map_pow, hn, map_zero]⟩
  have hpq : IsNilpotent ((p : ℕ) : Rigidified.Baway f ⧸ pIdeal p (Rigidified.Baway f)) :=
    ⟨1, by rw [pow_one, ← map_natCast (Ideal.Quotient.mk _) p, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl⟩
  have hc : t.IsGradedS ι ψ (Rigidified.awayHom f) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hp0 _
  have hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq _
  have hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ hpq _
  obtain ⟨L, hL⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p
    (Rigidified.jS ι ψ (Rigidified.awayHom f)) (isHausdorff_of_isNilpotent hp0) _ _ hγ hc

  obtain ⟨m, w, hw⟩ := exists_pow_smul_eq_coe p v

  letI : Algebra ℤ_[p] (Rigidified.Baway f) := ((Rigidified.awayHom f).comp (algebraMap ℤ_[p] B)).toAlgebra
  obtain ⟨z, hz⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_pow_smul_of_isAdmissible
    p ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht i (Rigidified.awayHom f) hp0 hc hcb hcΦf L hL w

  refine ⟨t.n + 1 + m, (hN x _).2 ⟨f, hf, hc, hcb, hcΦf, L, hL, z, ?_⟩⟩
  have hsm : (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) ^ (t.n + 1 + m) • v =
      (p : ℚ_[p]) ^ (t.n + 1) • fun j => ((w j : ℤ_[p]) : ℚ_[p]) := by
    rw [← hw, smul_smul, ← pow_add, map_natCast]
  rw [hsm]
  exact hz

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_mem_of_isAdmissible
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_mem_of_isAdmissible (solution)
