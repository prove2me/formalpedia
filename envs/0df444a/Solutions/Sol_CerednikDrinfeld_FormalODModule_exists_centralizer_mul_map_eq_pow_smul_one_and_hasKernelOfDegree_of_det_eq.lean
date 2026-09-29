-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8757027a-f20f-50bb-bb88-b4ef1fa6d76b

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalODModule_injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_exists_det_eq_mul_pow_of_hasKernelOfDegree
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instModulePadicInt MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace E185

section MatrixAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]

theorem smul_adjugate_mul_eq (A : Matrix n n R) (u : Rˣ) (x : R) (hA : A.det = (u : R) * x) :
    ((↑u⁻¹ : R) • A.adjugate) * A = x • (1 : Matrix n n R) := by
  rw [Matrix.smul_mul, Matrix.adjugate_mul, hA, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]

theorem map_smul_one (f : R →+* S) (x : R) :
    (x • (1 : Matrix n n R)).map f = f x • (1 : Matrix n n S) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem map_smul_eq (f : R →+* S) (x : R) (A : Matrix n n R) :
    (x • A).map f = f x • A.map f := by
  ext i j; simp

theorem mul_map_eq_smul_one_of (f : R →+* S) (A B : Matrix n n R) (x : R) (hBA : B * A = x • 1)
    (M : Matrix n n S) (s : S) (hM : M = s • B.map f) :
    M * A.map f = (s * f x) • (1 : Matrix n n S) := by
  subst hM
  rw [Matrix.smul_mul, ← Matrix.map_mul, hBA, map_smul_one, smul_smul]

theorem det_map_eq (f : R →+* S) (A : Matrix n n R) : (A.map f).det = f A.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

end MatrixAlgebra

section Padic

variable (p : ℕ) [Fact p.Prime]

theorem norm_coe_units (w : ℤ_[p]ˣ) : ‖((w : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  have h : IsUnit (w : ℤ_[p]) := Units.isUnit w
  have h1 : ‖(w : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp h
  simpa [PadicInt.norm_def] using h1

theorem eq_of_units_mul_pow_eq_pow (w : ℤ_[p]ˣ) (a b : ℕ)
    (h : ((w : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ a = (p : ℚ_[p]) ^ b) : a = b := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hn := congrArg (fun x : ℚ_[p] => ‖x‖) h
  simp only [norm_mul, norm_pow, norm_coe_units, one_mul, Padic.norm_p] at hn

  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  exact pow_right_injective₀ hp0 hp1.ne hn

end Padic

section Centralizer

open MvFormalGroup

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]

theorem isODHom_of_mem_centralizer (Φ : FormalODModule p B)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) :
    FormalODModule.IsODHom Φ Φ (e : MvFormalGroup.End Φ.F).toPowerSeries := by
  have hmem := Subring.mem_centralizer_iff.mp e.2
  refine ⟨IsLawHom.of_hom _, fun a => ?_, ?_⟩
  · have h := congrArg MvFormalGroup.Hom.toPowerSeries (hmem (Φ.actEnd a) (Or.inl ⟨a, rfl⟩))
    rw [MvFormalGroup.End.toPowerSeries_mul, MvFormalGroup.End.toPowerSeries_mul] at h
    exact h.symm
  · have h := congrArg MvFormalGroup.Hom.toPowerSeries (hmem Φ.varpiEnd (Or.inr rfl))
    rw [MvFormalGroup.End.toPowerSeries_mul, MvFormalGroup.End.toPowerSeries_mul] at h
    exact h.symm

end Centralizer

theorem core
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hinj : Function.Injective E) (m : ℕ)
    (hcof : ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}),
      E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hint : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
      (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (v : ℕ) (u : ℤ_[p]ˣ) (hA : A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ v) :
    ∃ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (c : ℕ),
      E e * A.map ((↑) : ℤ_[p] → ℚ_[p]) = ((p : ℚ_[p]) ^ (c + v)) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∧
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (4 * c + 2 * v)) ∧
      FormalODModule.IsODHom Φ Φ (e : MvFormalGroup.End Φ.F).toPowerSeries := by

  have hcoe : ((↑) : ℤ_[p] → ℚ_[p]) = ⇑(PadicInt.Coe.ringHom (p := p)) := rfl

  obtain ⟨e, he⟩ := hcof ((↑u⁻¹ : ℤ_[p]) • A.adjugate)
  have hBA := smul_adjugate_mul_eq A u ((p : ℤ_[p]) ^ v) hA
  have h1 : E e * A.map ((↑) : ℤ_[p] → ℚ_[p]) = ((p : ℚ_[p]) ^ (m + v)) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    rw [hcoe] at he ⊢
    rw [mul_map_eq_smul_one_of _ A _ _ hBA (E e) _ he, map_pow, map_natCast, pow_add]
  refine ⟨e, m, h1, ?_, isODHom_of_mem_centralizer Φ e⟩

  have hE' : Function.Injective E ∧ ∃ m : ℕ,
      (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e, E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
      (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p])) := by
    refine ⟨hinj, m + 1, fun A' => ?_, fun e' => ?_⟩
    · obtain ⟨e', he'⟩ := hcof ((p : ℤ_[p]) • A')
      refine ⟨e', ?_⟩
      rw [he', hcoe, map_smul_eq, smul_smul, map_natCast, pow_succ]
    · obtain ⟨A', hA'⟩ := hint e'
      refine ⟨(p : ℤ_[p]) ^ m • A', ?_⟩
      rw [hcoe] at hA' ⊢
      rw [map_smul_eq, ← hA', smul_smul, map_pow, map_natCast, pow_succ]

  have hdetA : (A.map ((↑) : ℤ_[p] → ℚ_[p])).det = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ v := by
    rw [hcoe, det_map_eq, hA, map_mul, map_pow, map_natCast]
  have hdet : (E e).det * (((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ v) = (p : ℚ_[p]) ^ (m + v) * (p : ℚ_[p]) ^ (m + v) := by
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, hdetA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    rw [this]; ring
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdet0 : (E e).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact (mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hp0)) hdet.symm
  have hunit : IsUnit (E e) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet0.isUnit
  obtain ⟨m', hm'⟩ :=
    CerednikDrinfeld.SpecialFormal.exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
      k ι Φ hΦ hΦ4 E hE' e hunit.unit hunit.unit_spec
  obtain ⟨u', hu'⟩ :=
    CerednikDrinfeld.SpecialFormal.exists_det_eq_mul_pow_of_hasKernelOfDegree
      k ι Φ hΦ hΦ4 E hE' e m' hm'

  have hexp : m' + v = (m + v) + (m + v) := by
    apply eq_of_units_mul_pow_eq_pow p (u' * u)
    rw [hu'] at hdet
    rw [Units.val_mul, PadicInt.coe_mul, pow_add, pow_add]
    calc ((u' : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) ^ m' * (p : ℚ_[p]) ^ v)
        = ((u' : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ m' * (((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ v) := by ring
      _ = (p : ℚ_[p]) ^ (m + v) * (p : ℚ_[p]) ^ (m + v) := hdet
  have hm : 2 * m' = 4 * m + 2 * v := by omega
  rw [← hm]
  exact hm'

end E185

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
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hNe : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))))
    (hE : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) ∧
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p • Ne (rΦ w) = rΦ (A.mulVec w))
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (v : ℕ) (u : ℤ_[p]ˣ) (hA : A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ v) :
    ∃ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (c : ℕ),
      E e * A.map ((↑) : ℤ_[p] → ℚ_[p]) = ((p : ℚ_[p]) ^ (c + v)) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∧
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (4 * c + 2 * v)) ∧
      FormalODModule.IsODHom Φ Φ (e : MvFormalGroup.End Φ.F).toPowerSeries := by
  have h2 := CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
    p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ E hNe hE
  obtain ⟨hinj, m, hcof⟩ := h2
  exact E185.core p k ι Φ hΦ hΦ4 E hinj m hcof (fun e => (hE e).imp fun A h => h.1) A v u hA

end S_CerednikDrinfeld_FormalODModule_exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq (solution)
