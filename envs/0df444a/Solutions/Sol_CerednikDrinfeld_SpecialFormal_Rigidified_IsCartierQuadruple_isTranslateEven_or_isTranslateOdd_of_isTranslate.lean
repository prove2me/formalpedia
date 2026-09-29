-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isTranslateEven_or_isTranslateOdd_of_isTranslate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1d0d32c1-1194-5f6e-ae50-036e84e16a3b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_eq_latticeMap_of_isTranslate_of_even
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_eq_latticeMap_of_isTranslate_of_odd
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isTranslateEven_or_isTranslateOdd_of_isTranslate
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.FormalODModule.frobTwist_F CerednikDrinfeld.FormalODModule.frobTwist_frobTwist CerednikDrinfeld.FormalODModule.frobTwist_varpi CerednikDrinfeld.FormalODModule.frobTwist_act"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ)
    (hEinj : Function.Injective E)
    (hEord : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEcompat : (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = E e)
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t')
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) Q') :
    (∃ c : ℚ_[p]ˣ, Q.IsTranslateEven g c Q') ∨
      (∃ c₀ c₁ : ℚ_[p]ˣ, Q.IsTranslateOdd g c₀ c₁ Q') := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m'
  ·
    left
    refine ⟨Units.mk0 ((p : ℚ_[p]) ^ j) (pow_ne_zero _ hp0), ?_⟩
    have hc : ((Units.mk0 ((p : ℚ_[p]) ^ j) (pow_ne_zero _ hp0) : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) ^ j := rfl
    have hN := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_eq_latticeMap_of_isTranslate_of_even
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψ hB E m hEinj hEord hEcompat e m' hker g hg t t' ht ht' htr Q Q' hQ hQ' j hj _ hc
    obtain ⟨τ₀, τ₁, h1, h2, h3, h4⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_even
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψ hB E m hEinj hEord hEcompat e m' hker g hg t t' ht ht' htr Q Q' hQ hQ' j hj _ hc
    exact ⟨{ N₀_eq := fun x => (hN x).1, N₁_eq := fun x => (hN x).2, τ₀ := τ₀, τ₁ := τ₁,
             τ₁_Pi₀ := h1, τ₀_Pi₁ := h2, τ₀_u₀ := h3, τ₁_u₁ := h4 }⟩
  ·
    right
    refine ⟨Units.mk0 ((p : ℚ_[p]) ^ (j + 1)) (pow_ne_zero _ hp0), Units.mk0 ((p : ℚ_[p]) ^ j) (pow_ne_zero _ hp0), ?_⟩
    have hc₀ : ((Units.mk0 ((p : ℚ_[p]) ^ (j + 1)) (pow_ne_zero _ hp0) : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) ^ (j + 1) := rfl
    have hc₁ : ((Units.mk0 ((p : ℚ_[p]) ^ j) (pow_ne_zero _ hp0) : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) ^ j := rfl
    have hN := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_eq_latticeMap_of_isTranslate_of_odd
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψ hB E m hEinj hEord hEcompat e m' hker g hg t t' ht ht' htr Q Q' hQ hQ' j hj _ _ hc₀ hc₁
    obtain ⟨σ₀, σ₁, h1, h2, h3, h4⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
      p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ ψ hB E m hEinj hEord hEcompat e m' hker g hg t t' ht ht' htr Q Q' hQ hQ' j hj _ _ hc₀ hc₁
    refine ⟨{ c₀_eq := ?_, N₀_eq := fun x => (hN x).1, N₁_eq := fun x => (hN x).2, σ₀ := σ₀, σ₁ := σ₁,
              σ₁_Pi₁ := h1, σ₀_Pi₀ := h2, σ₀_u₀ := h3, σ₁_u₁ := h4 }⟩
    rw [hc₀, hc₁, pow_succ']
    congr 1

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isTranslateEven_or_isTranslateOdd_of_isTranslate
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isTranslateEven_or_isTranslateOdd_of_isTranslate (solution)
