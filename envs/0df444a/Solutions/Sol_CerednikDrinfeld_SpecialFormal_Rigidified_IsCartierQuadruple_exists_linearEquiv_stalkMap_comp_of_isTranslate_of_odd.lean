-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/800001b0-6ac1-502e-958e-5e56f5c0635b

import Mathlib
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_iff_isEtaSection_of_isTranslate_of_odd
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_WittVector_ringHom_map_frobenius_of_finite
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.FormalODModule.frobTwist_F CerednikDrinfeld.FormalODModule.frobTwist_frobTwist CerednikDrinfeld.FormalODModule.frobTwist_varpi CerednikDrinfeld.FormalODModule.frobTwist_act"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace K74TO

open CerednikDrinfeld

variable (p : ℕ) [Fact p.Prime]

theorem frobenius_frobenius (a : Zp2 p) :
    WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← pow_two]

  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  rw [← hcard]
  exact FiniteField.pow_card _

theorem frobenius_comp_frobenius :
    (WittVector.frobenius : Zp2 p →+* Zp2 p).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) = RingHom.id _ := by
  exact RingHom.ext (fun a => frobenius_frobenius p a)

theorem lieZero_comp_frobenius_and_lieOne_comp_frobenius {B : Type} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B) :
    X.lieZero (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieOne j ∧
      X.lieOne (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieZero j := by
  constructor
  · rfl
  · simp only [FormalODModule.lieOne, FormalODModule.lieZero, RingHom.comp_apply, frobenius_frobenius]

end K74TO

namespace K78TO

p2m_open "CerednikDrinfeld CerednikDrinfeld.FormalODModule~lieZero_comp_frobenius"

theorem frobenius_comp_frobenius_Zp2 (p : ℕ) [Fact p.Prime] :
    (WittVector.frobenius : Zp2 p →+* Zp2 p).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) = RingHom.id _ :=
  K74TO.frobenius_comp_frobenius p

theorem lieZero_comp_frobenius {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B) :
    X.lieZero (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieOne j ∧
      X.lieOne (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieZero j :=
  K74TO.lieZero_comp_frobenius_and_lieOne_comp_frobenius p X j

theorem frobenius_comp_eq_comp_frobenius (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) :
    (WittVector.frobenius : WittVector p k →+* WittVector p k).comp ι = ι.comp (WittVector.frobenius : Zp2 p →+* Zp2 p) :=
  RingHom.ext fun x => (WittVector.ringHom_map_frobenius_of_finite p ι x).symm

theorem frobenius_pow_comp_eq (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) (n : ℕ) :
    ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ n).comp ι = ι.comp ((WittVector.frobenius : Zp2 p →+* Zp2 p) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, RingHom.mul_def, RingHom.mul_def, RingHom.comp_assoc, frobenius_comp_eq_comp_frobenius, ← RingHom.comp_assoc, ih,
      RingHom.comp_assoc]

theorem frobenius_Zp2_pow_odd (p : ℕ) [Fact p.Prime] (j : ℕ) :
    (WittVector.frobenius : Zp2 p →+* Zp2 p) ^ (2 * j + 1) = WittVector.frobenius := by
  rw [pow_succ, pow_mul]
  have : (WittVector.frobenius : Zp2 p →+* Zp2 p) ^ 2 = 1 := by
    rw [sq, RingHom.mul_def, frobenius_comp_frobenius_Zp2]; rfl
  rw [this, one_pow, one_mul]

end K78TO

open CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.SpecialFormal.Rigidified in

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
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) Q')
    (j : ℕ) (hm' : m' = 2 * j + 1) (c₀ c₁ : ℚ_[p]ˣ)
    (hc₀ : (c₀ : ℚ_[p]) = (p : ℚ_[p]) ^ (j + 1)) (hc₁ : (c₁ : ℚ_[p]) = (p : ℚ_[p]) ^ j) :
    ∃ (σ₀ : Q.T₁ ≃ₗ[B] Q'.T₀) (σ₁ : Q.T₀ ≃ₗ[B] Q'.T₁),
      (∀ s, σ₁ (Q.Pi₁ s) = Q'.Pi₀ (σ₀ s)) ∧ (∀ s, σ₀ (Q.Pi₀ s) = Q'.Pi₁ (σ₁ s)) ∧
      (∀ (x : PrimeSpectrum B) (w : Fin 2 → ℚ_[p]) (hw : w ∈ Q.N₁ x)
        (hw' : ((scalarGL c₀ * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec w ∈ Q'.N₀ x),
        Q'.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hw'⟩ : ↥(Q'.N₀ x))) =
          LocalizedModule.map x.asIdeal.primeCompl σ₀.toLinearMap
            (Q.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨w, hw⟩ : ↥(Q.N₁ x))))) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x)
        (hv' : ((scalarGL c₁ * g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).mulVec v ∈ Q'.N₁ x),
        Q'.u₁ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
          LocalizedModule.map x.asIdeal.primeCompl σ₁.toLinearMap
            (Q.u₀ x ((1 : locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))))) := by
  haveI : PerfectRing k p := IsAlgClosed.perfectRing k p

  obtain ⟨X', n', ρ'⟩ := t'
  have hX : X' = t.X := htr.1
  subst hX

  have hj : structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) = (structureMap ι ψ).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) := by
    show (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')).comp ι = (ψ.comp ι).comp _
    rw [RingHom.comp_assoc, K78TO.frobenius_pow_comp_eq, hm', K78TO.frobenius_Zp2_pow_odd, ← RingHom.comp_assoc]
  obtain ⟨h0, h1⟩ := K78TO.lieZero_comp_frobenius t.X (structureMap ι ψ)
  have hl0 : t.X.lieZero (structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m'))) = t.X.lieOne (structureMap ι ψ) := by rw [hj, h0]
  have hl1 : t.X.lieOne (structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m'))) = t.X.lieZero (structureMap ι ψ) := by rw [hj, h1]

  have hOD := hQ.1
  have hOD' := hQ'.1
  obtain ⟨τ₀, τ₁, hT0, hT1, hN⟩ := hQ.2
  obtain ⟨τ'₀, τ'₁, hT0', hT1', hN'⟩ := hQ'.2

  have hpf : ∀ f : B, IsNilpotent ((p : ℕ) : Rigidified.Baway f) := fun f => by
    obtain ⟨N, hN⟩ := hB
    exact ⟨N, by rw [← map_natCast (Rigidified.awayHom f), ← map_pow, hN, map_zero]⟩
  have hp1 : ∀ f : B, IsNilpotent ((p : ℕ) : Rigidified.Baway f ⧸ pIdeal p (Rigidified.Baway f)) := fun f =>
    ⟨1, by rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway f)))]
           exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩
  refine ⟨τ₁.trans ((LinearEquiv.ofEq _ _ hl0).symm.trans τ'₀.symm), τ₀.trans ((LinearEquiv.ofEq _ _ hl1).symm.trans τ'₁.symm),
    fun s => ?_, fun s => ?_, ?_, ?_⟩
  · show τ'₁.symm ((LinearEquiv.ofEq _ _ hl1).symm (τ₀ (Q.Pi₁ s))) = Q'.Pi₀ (τ'₀.symm ((LinearEquiv.ofEq _ _ hl0).symm (τ₁ s)))
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply, hT1, hT0', LinearEquiv.apply_symm_apply, LinearEquiv.ofEq_symm,
      LinearEquiv.coe_ofEq_apply]
  · show τ'₀.symm ((LinearEquiv.ofEq _ _ hl0).symm (τ₁ (Q.Pi₀ s))) = Q'.Pi₁ (τ'₁.symm ((LinearEquiv.ofEq _ _ hl1).symm (τ₀ s)))
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply, hT0, hT1', LinearEquiv.apply_symm_apply, LinearEquiv.ofEq_symm,
      LinearEquiv.coe_ofEq_apply]
  ·
    intro x w hw hw'
    obtain ⟨hN0, hN1, hu0, hu1⟩ := hN hOD x
    obtain ⟨hN0', hN1', hu0', hu1'⟩ := hN' hOD' x
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN1 w).mp hw
    obtain ⟨xz, rfl⟩ := GradedCartierModuleData.nMk_surjective _ z
    have hc' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hpf f) _
    have hcb' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedSbar ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
    have hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
    obtain ⟨I, -, hInMk, hIL⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_iff_isEtaSection_of_isTranslate_of_odd p k ι Φ hΦ hΦ4
        hcΦ rΦ hrΦ ψ hB E m hEinj hEord hEcompat e m' hker g hg t ht n' ρ' ht' htr hOD hOD' j hm' c₀ c₁ hc₀ hc₁ f
        hc hcb hcΦf hc' hcb' hcΦf'
    obtain ⟨hL', hiff⟩ := hIL L hL
    have hz' := (hiff _ w).1.mp hz
    obtain ⟨m₁, s₁, b₁, hmu₁, hQu₁, htan₁⟩ := hu1 w hw f hf hc hcb hcΦf L hL _ hz
    obtain ⟨m₂, s₂, b₂, hmu₂, hQu₂, htan₂⟩ := hu0' _ hw' f hf hc' hcb' hcΦf' (I.comp L) hL' (I _) hz'

    have hmm₁ : m₁ - xz.1 ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
      exact hmu₁
    obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f)) hc').M, x₂ = xz.1 := ⟨_, rfl⟩
    have hmm₂ : m₂ - x₂ ∈ ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f)) hc').vRange := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
      refine hmu₂.trans ?_
      show ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f)) hc').toLieQuot (I _) = _
      rw [hInMk, hx₂]
      rfl
    have htan : tangent m₁ = tangent m₂ := by
      obtain ⟨y₁, hy₁⟩ := hmm₁
      obtain ⟨y₂, hy₂⟩ := hmm₂
      have h₁ : tangent (m₁ - xz.1) = 0 := by rw [← hy₁]; exact tangent_verschiebungInt y₁
      have h₂ : tangent (m₂ - x₂) = 0 := by rw [← hy₂]; exact tangent_verschiebungInt y₂
      have e₁ := AddMonoidHom.map_sub (tangent (p := p) (Φ := (t.XS (Rigidified.awayHom f)).F)) m₁ xz.1
      have e₂ := AddMonoidHom.map_sub (tangent (p := p) (Φ := (({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).F)) m₂ x₂
      have h₁' := sub_eq_zero.mp (e₁.symm.trans h₁)
      have h₂' := sub_eq_zero.mp (e₂.symm.trans h₂)
      rw [hx₂] at h₂'
      exact h₁'.trans h₂'.symm

    have key : ∀ i : Fin 2, ∃ u : x.asIdeal.primeCompl,
        (u : B) * ((b₂ : B) * (τ₁ s₁ : t.X.Lie) i) = (u : B) * ((b₁ : B) * (τ'₀ s₂ : t.X.Lie) i) := by
      intro i
      apply (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Rigidified.Bloc x)).mp
      show Rigidified.locHom x _ = Rigidified.locHom x _
      rw [map_mul, map_mul, htan₁ i, htan₂ i, htan]
      ring
    obtain ⟨u₀, hu₀⟩ := key 0
    obtain ⟨w₁, hw₁⟩ := key 1
    have hvec : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • (τ₁ s₁ : t.X.Lie) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • (τ'₀ s₂ : t.X.Lie) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (w₁ : B) * hu₀
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (u₀ : B) * hw₁
    have hsub : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • (LinearEquiv.ofEq _ _ hl0).symm (τ₁ s₁) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • τ'₀ s₂ := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
      exact hvec
    have hT : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • τ'₀.symm ((LinearEquiv.ofEq _ _ hl0).symm (τ₁ s₁)) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • s₂ := by
      apply τ'₀.injective
      rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
      exact hsub
    rw [hQu₂, hQu₁, LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨u₀ * w₁, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearEquiv.coe_coe, LinearEquiv.trans_apply, smul_smul]
    exact hT.symm
  ·
    intro x w hw hw'
    obtain ⟨hN0, hN1, hu0, hu1⟩ := hN hOD x
    obtain ⟨hN0', hN1', hu0', hu1'⟩ := hN' hOD' x
    obtain ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩ := (hN0 w).mp hw
    obtain ⟨xz, rfl⟩ := GradedCartierModuleData.nMk_surjective _ z
    have hc' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hpf f) _
    have hcb' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedSbar ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
    have hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f) :=
      CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
    obtain ⟨I, -, hInMk, hIL⟩ :=
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_iff_isEtaSection_of_isTranslate_of_odd p k ι Φ hΦ hΦ4
        hcΦ rΦ hrΦ ψ hB E m hEinj hEord hEcompat e m' hker g hg t ht n' ρ' ht' htr hOD hOD' j hm' c₀ c₁ hc₀ hc₁ f
        hc hcb hcΦf hc' hcb' hcΦf'
    obtain ⟨hL', hiff⟩ := hIL L hL
    have hz' := (hiff _ w).2.mp hz
    obtain ⟨m₁, s₁, b₁, hmu₁, hQu₁, htan₁⟩ := hu0 w hw f hf hc hcb hcΦf L hL _ hz
    obtain ⟨m₂, s₂, b₂, hmu₂, hQu₂, htan₂⟩ := hu1' _ hw' f hf hc' hcb' hcΦf' (I.comp L) hL' (I _) hz'

    have hmm₁ : m₁ - xz.1 ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
      exact hmu₁
    obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f)) hc').M, x₂ = xz.1 := ⟨_, rfl⟩
    have hmm₂ : m₂ - x₂ ∈ ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f)) hc').vRange := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
      refine hmu₂.trans ?_
      show ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) (Rigidified.awayHom f)) hc').toLieQuot (I _) = _
      rw [hInMk, hx₂]
      rfl
    have htan : tangent m₁ = tangent m₂ := by
      obtain ⟨y₁, hy₁⟩ := hmm₁
      obtain ⟨y₂, hy₂⟩ := hmm₂
      have h₁ : tangent (m₁ - xz.1) = 0 := by rw [← hy₁]; exact tangent_verschiebungInt y₁
      have h₂ : tangent (m₂ - x₂) = 0 := by rw [← hy₂]; exact tangent_verschiebungInt y₂
      have e₁ := AddMonoidHom.map_sub (tangent (p := p) (Φ := (t.XS (Rigidified.awayHom f)).F)) m₁ xz.1
      have e₂ := AddMonoidHom.map_sub (tangent (p := p) (Φ := (({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).F)) m₂ x₂
      have h₁' := sub_eq_zero.mp (e₁.symm.trans h₁)
      have h₂' := sub_eq_zero.mp (e₂.symm.trans h₂)
      rw [hx₂] at h₂'
      exact h₁'.trans h₂'.symm

    have key : ∀ i : Fin 2, ∃ u : x.asIdeal.primeCompl,
        (u : B) * ((b₂ : B) * (τ₀ s₁ : t.X.Lie) i) = (u : B) * ((b₁ : B) * (τ'₁ s₂ : t.X.Lie) i) := by
      intro i
      apply (IsLocalization.eq_iff_exists x.asIdeal.primeCompl (Rigidified.Bloc x)).mp
      show Rigidified.locHom x _ = Rigidified.locHom x _
      rw [map_mul, map_mul, htan₁ i, htan₂ i, htan]
      ring
    obtain ⟨u₀, hu₀⟩ := key 0
    obtain ⟨w₁, hw₁⟩ := key 1
    have hvec : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • (τ₀ s₁ : t.X.Lie) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • (τ'₁ s₂ : t.X.Lie) := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (w₁ : B) * hu₀
      · simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (u₀ : B) * hw₁
    have hsub : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • (LinearEquiv.ofEq _ _ hl1).symm (τ₀ s₁) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • τ'₁ s₂ := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_smul, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
      exact hvec
    have hT : (((u₀ : B) * (w₁ : B)) * (b₂ : B)) • τ'₁.symm ((LinearEquiv.ofEq _ _ hl1).symm (τ₀ s₁)) =
        (((u₀ : B) * (w₁ : B)) * (b₁ : B)) • s₂ := by
      apply τ'₁.injective
      rw [map_smul, map_smul, LinearEquiv.apply_symm_apply]
      exact hsub
    rw [hQu₂, hQu₁, LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨u₀ * w₁, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearEquiv.coe_coe, LinearEquiv.trans_apply, smul_smul]
    exact hT.symm

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_exists_linearEquiv_stalkMap_comp_of_isTranslate_of_odd (solution)
