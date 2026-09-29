-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.N_eq_latticeMap_of_isTranslate_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7bf00daa-f4be-5910-b5d4-554491597529

import Mathlib
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_iff_isEtaSection_of_isTranslate_of_odd
import Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius
import Theorems.Thm_WittVector_ringHom_map_frobenius_of_finite
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
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

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_eq_latticeMap_of_isTranslate_of_odd
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic Matrix

namespace B28SM

variable {p : ℕ} [Fact p.Prime]

theorem frobenius_frobenius_zp2 (x : Zp2 p) :
    WittVector.frobenius (WittVector.frobenius x) = x := by
  ext n
  simp only [WittVector.coeff_frobenius_charP]
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  rw [← pow_mul, ← pow_two, ← hcard]; exact FiniteField.pow_card _

theorem frobenius_pow_two_mul_zp2 (j : ℕ) (x : Zp2 p) :
    ((WittVector.frobenius : Zp2 p →+* Zp2 p) ^ (2 * j)) x = x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, pow_add, RingHom.mul_def, RingHom.comp_apply, pow_two, RingHom.mul_def, RingHom.comp_apply,
      frobenius_frobenius_zp2, ih]

theorem frobenius_pow_comp_eq (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) (n : ℕ) (x : Zp2 p) :
    ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ n) (ι x) =
      ι (((WittVector.frobenius : Zp2 p →+* Zp2 p) ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, pow_succ', RingHom.mul_def, RingHom.comp_apply,
      WittVector.ringHom_map_frobenius_of_finite]

theorem structureMap_comp_frobenius_pow_two_mul (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (j : ℕ) :
    structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j))) = structureMap ι ψ := by
  refine RingHom.ext fun x => ?_
  show ψ (((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j)) (ι x)) = ψ (ι x)
  rw [frobenius_pow_comp_eq, frobenius_pow_two_mul_zp2]

theorem structureMap_comp_frobenius_pow_two_mul_add_one (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k) {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (j : ℕ) :
    structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) =
      (structureMap ι ψ).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) := by
  refine RingHom.ext fun x => ?_
  show ψ (((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1)) (ι x)) = ψ (ι (WittVector.frobenius x))
  rw [frobenius_pow_comp_eq, pow_succ, RingHom.mul_def, RingHom.comp_apply, frobenius_pow_two_mul_zp2]

end B28SM

namespace LO7

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [hp : Fact p.Prime]

theorem sigmaShiftI {C : Type} [CommRing C] (X : FormalODModule p C) (j₁ j₂ : Zp2 p →+* C)
    (h : j₁.comp (WittVector.frobenius : Zp2 p →+* Zp2 p) = j₂)
    (hc₁ : IsCompl (X.gradedPiece j₁ 0) (X.gradedPiece j₁ 1)) (hc₂ : IsCompl (X.gradedPiece j₂ 0) (X.gradedPiece j₂ 1))
    (I : (X.toGradedCartierModuleData j₁ hc₁).NMod →+ (X.toGradedCartierModuleData j₂ hc₂).NMod)
    (hI : ∀ x y : CartierModule p X.F, I ((X.toGradedCartierModuleData j₁ hc₁).nMk (x, y)) = (X.toGradedCartierModuleData j₂ hc₂).nMk (x, y)) :
    Function.Bijective I ∧
    (∀ z, I ((X.toGradedCartierModuleData j₁ hc₁).nVarpi z) = (X.toGradedCartierModuleData j₂ hc₂).nVarpi (I z)) ∧
    (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j₁ hc₁).NMod),
        z ∈ (X.toGradedCartierModuleData j₁ hc₁).nPiece i ↔ I z ∈ (X.toGradedCartierModuleData j₂ hc₂).nPiece (i + 1)) ∧
    (∀ (L : CartierModule p X.F →+ (X.toGradedCartierModuleData j₁ hc₁).NMod)
      (hL : (X.toGradedCartierModuleData j₁ hc₁).IsCartierLMap L),
      ∃ hL' : (X.toGradedCartierModuleData j₂ hc₂).IsCartierLMap (I.comp L),
        (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j₁ hc₁).NMod),
            z ∈ (X.toGradedCartierModuleData j₁ hc₁).etaPiece L hL.map_verschiebung i ↔
              I z ∈ (X.toGradedCartierModuleData j₂ hc₂).etaPiece (I.comp L) hL'.map_verschiebung (i + 1)) ∧
        ((X.toGradedCartierModuleData j₁ hc₁).IsCanonicalLMap L ↔
          (X.toGradedCartierModuleData j₂ hc₂).IsCanonicalLMap (I.comp L))) := by
  subst h
  exact CerednikDrinfeld.FormalODModule.nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius p X j₁
    hc₁ hc₂ I hI

theorem gl_mulVec_inv_mulVec {K : Type} [Field K] (M : Matrix.GeneralLinearGroup (Fin 2) K) (w : Fin 2 → K) :
    ((M : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_latticeMap_iff_inv_mulVec_mem {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (h : Matrix.GeneralLinearGroup (Fin 2) K) (N : Submodule R (Fin 2 → K)) (v : Fin 2 → K) :
    v ∈ latticeMap h N ↔ ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ N := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro hv
    exact ⟨_, hv, by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

theorem isEtaSection_congr {O : Type} [CommRing O] (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ) {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    {L₁ L₂ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod}
    (hL₁ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L₁)
    (hL₂ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L₂)
    (e : L₁ = L₂) {z₁ z₂ : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod} (ez : z₁ = z₂)
    {v₁ v₂ : Fin 2 → ℚ_[p]} (ev : v₁ = v₂) (i : Fin 2) :
    t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L₁ hL₁ i z₁ v₁ ↔ t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L₂ hL₂ i z₂ v₂ := by
  subst e ez ev
  exact Iff.rfl

end LO7

open LO7

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
    ∀ x : PrimeSpectrum B,
      Q'.N₀ x = latticeMap (scalarGL c₀ * g⁻¹) (Q.N₁ x) ∧ Q'.N₁ x = latticeMap (scalarGL c₁ * g⁻¹) (Q.N₀ x) := by
  classical
  intro x
  obtain ⟨X', n', ρ'⟩ := t'
  have hX : X' = t.X := htr.1
  subst hX
  subst hm'
  haveI : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  have hsm : structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) = (structureMap ι ψ).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) :=
    B28SM.structureMap_comp_frobenius_pow_two_mul_add_one k ι ψ j
  have hσσ : (WittVector.frobenius : Zp2 p →+* Zp2 p).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) = RingHom.id (Zp2 p) := RingHom.ext (fun x => B28SM.frobenius_frobenius_zp2 x)
  have hjS2 : ∀ f : B, (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f)).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) = Rigidified.jS ι ψ (Rigidified.awayHom f) := fun f => by
    show ((Rigidified.awayHom f).comp (structureMap ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))))).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) = (Rigidified.awayHom f).comp (structureMap ι ψ)
    rw [hsm, RingHom.comp_assoc, RingHom.comp_assoc, hσσ, RingHom.comp_id]
  have hOD := hQ.1
  have hOD' := hQ'.1
  obtain ⟨τ₀, τ₁, -, -, hN⟩ := hQ.2
  obtain ⟨τ₀', τ₁', -, -, hN'⟩ := hQ'.2
  obtain ⟨hN0, hN1, -, -⟩ := hN hOD x
  obtain ⟨hN0', hN1', -, -⟩ := hN' hOD' x
  have hS : ∀ f : B, IsNilpotent ((p : ℕ) : Rigidified.Baway f) := fun f => by
    obtain ⟨N, hN⟩ := hB
    exact ⟨N, by rw [← map_natCast (Rigidified.awayHom f) p, ← map_pow, hN, map_zero]⟩
  have hp1 : ∀ f : B, IsNilpotent ((p : ℕ) : Rigidified.Baway f ⧸ pIdeal p (Rigidified.Baway f)) := fun f =>
    ⟨1, by rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p (Rigidified.Baway f)))]
           exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩
  have gS : ∀ f : B, t.IsGradedS ι ψ (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hS f) _
  have gSb : ∀ f : B, t.IsGradedSbar ι ψ (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
  have gΦ : ∀ f : B, Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
  have gS' : ∀ f : B, ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hS f) _
  have gSb' : ∀ f : B, ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedSbar ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
  have gΦ' : ∀ f : B, Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f) := fun f =>
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p _ (hp1 f) _
  have UA := fun f : B =>
    CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_iff_isEtaSection_of_isTranslate_of_odd p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ
      ψ hB E m hEinj hEord hEcompat e (2 * j + 1) hker g hg t ht n' ρ' ht' htr hOD hOD' j rfl c₀ c₁ hc₀ hc₁ f
      (gS f) (gSb f) (gΦ f) (gS' f) (gSb' f) (gΦ' f)
  have main0 : ∀ v : Fin 2 → ℚ_[p],
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
          (hcb' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedSbar ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
          (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
          (L : _) (hL : ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc').IsCanonicalLMap L),
          ∃ z, ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsEtaSection ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) hOD' (Rigidified.awayHom f) hc' hcb' hcΦf' L hL 0 z v) ↔
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z ((((scalarGL c₀ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v)) := by
    intro v
    constructor
    · rintro ⟨f, hf, hc', hcb', hcΦf', L', hL', z', hz'⟩
      obtain ⟨I, hIbij, hInMk, hIL⟩ := UA f
      have hInMk2 : ∀ a b : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F,
          I (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) (gS f)).nMk (a, b)) =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f)) (gS' f)).nMk (a, b) :=
        fun a b => hInMk (a, b)
      let eI := AddEquiv.ofBijective I hIbij
      let J : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f)) (gS' f)).NMod →+
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) (gS f)).NMod :=
        eI.symm.toAddMonoidHom
      have hJ : ∀ a b : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F,
          J (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f)) (gS' f)).nMk (a, b)) =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) (gS f)).nMk (a, b) := fun a b => by
        rw [← hInMk2 a b]
        exact eI.symm_apply_apply _
      obtain ⟨-, -, -, hJL⟩ := sigmaShiftI (t.XS (Rigidified.awayHom f)) (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
        (Rigidified.jS ι ψ (Rigidified.awayHom f)) (hjS2 f) (gS' f) (gS f) J hJ
      obtain ⟨-, -, hJcan⟩ := hJL L' hL'.isCartierLMap
      have hLJ := hJcan.mp hL'
      obtain ⟨hL2, hiff⟩ := hIL _ hLJ
      have e1 : AddMonoidHom.comp (M := MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) I
          (AddMonoidHom.comp (M := MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) J L') = L' := by
        ext a
        exact eI.apply_symm_apply (L' a)
      have e2 : I (J z') = z' := eI.apply_symm_apply z'
      have ev : ((scalarGL c₀ * g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ ((((scalarGL c₀ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v) = v := gl_mulVec_inv_mulVec _ v
      have h2 := (isEtaSection_congr ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' (Rigidified.awayHom f) hc' hcb' hcΦf' hL2 hL' e1 e2 ev 0).mpr hz'
      exact ⟨f, hf, gS f, gSb f, gΦ f, _, hLJ, J z', ((hiff (J z') ((((scalarGL c₀ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v)).1).mpr h2⟩
    · rintro ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩
      obtain ⟨I, hIbij, hInMk, hIL⟩ := UA f
      obtain ⟨hL2, hiff⟩ := hIL L hL
      refine ⟨f, hf, gS' f, gSb' f, gΦ' f, _, hL2, I z, ?_⟩
      have h1 := ((hiff z ((((scalarGL c₀ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v)).1).mp hz
      rwa [gl_mulVec_inv_mulVec] at h1

  have main1 : ∀ v : Fin 2 → ℚ_[p],
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
          (hcb' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsGradedSbar ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
          (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
          (L : _) (hL : ((({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc').IsCanonicalLMap L),
          ∃ z, ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsEtaSection ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) hOD' (Rigidified.awayHom f) hc' hcb' hcΦf' L hL 1 z v) ↔
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z ((((scalarGL c₁ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v)) := by
    intro v
    constructor
    · rintro ⟨f, hf, hc', hcb', hcΦf', L', hL', z', hz'⟩
      obtain ⟨I, hIbij, hInMk, hIL⟩ := UA f
      have hInMk2 : ∀ a b : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F,
          I (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) (gS f)).nMk (a, b)) =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f)) (gS' f)).nMk (a, b) :=
        fun a b => hInMk (a, b)
      let eI := AddEquiv.ofBijective I hIbij
      let J : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f)) (gS' f)).NMod →+
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) (gS f)).NMod :=
        eI.symm.toAddMonoidHom
      have hJ : ∀ a b : MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F,
          J (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f)) (gS' f)).nMk (a, b)) =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) (gS f)).nMk (a, b) := fun a b => by
        rw [← hInMk2 a b]
        exact eI.symm_apply_apply _
      obtain ⟨-, -, -, hJL⟩ := sigmaShiftI (t.XS (Rigidified.awayHom f)) (Rigidified.jS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) (Rigidified.awayHom f))
        (Rigidified.jS ι ψ (Rigidified.awayHom f)) (hjS2 f) (gS' f) (gS f) J hJ
      obtain ⟨-, -, hJcan⟩ := hJL L' hL'.isCartierLMap
      have hLJ := hJcan.mp hL'
      obtain ⟨hL2, hiff⟩ := hIL _ hLJ
      have e1 : AddMonoidHom.comp (M := MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) I
          (AddMonoidHom.comp (M := MvFormalGroup.CartierModule p (t.XS (Rigidified.awayHom f)).F) J L') = L' := by
        ext a
        exact eI.apply_symm_apply (L' a)
      have e2 : I (J z') = z' := eI.apply_symm_apply z'
      have ev : ((scalarGL c₁ * g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ ((((scalarGL c₁ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v) = v := gl_mulVec_inv_mulVec _ v
      have h2 := (isEtaSection_congr ι hcΦ rΦ (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ (2 * j + 1))) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' (Rigidified.awayHom f) hc' hcb' hcΦf' hL2 hL' e1 e2 ev 1).mpr hz'
      exact ⟨f, hf, gS f, gSb f, gΦ f, _, hLJ, J z', ((hiff (J z') ((((scalarGL c₁ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v)).2).mpr h2⟩
    · rintro ⟨f, hf, hc, hcb, hcΦf, L, hL, z, hz⟩
      obtain ⟨I, hIbij, hInMk, hIL⟩ := UA f
      obtain ⟨hL2, hiff⟩ := hIL L hL
      refine ⟨f, hf, gS' f, gSb' f, gΦ' f, _, hL2, I z, ?_⟩
      have h1 := ((hiff z ((((scalarGL c₁ * g⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ v)).2).mp hz
      rwa [gl_mulVec_inv_mulVec] at h1

  refine ⟨?_, ?_⟩
  · ext v
    rw [hN0' v, mem_latticeMap_iff_inv_mulVec_mem, hN1]
    exact main0 v
  · ext v
    rw [hN1' v, mem_latticeMap_iff_inv_mulVec_mem, hN0]
    exact main1 v

end S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_eq_latticeMap_of_isTranslate_of_odd
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_N_eq_latticeMap_of_isTranslate_of_odd (solution)
