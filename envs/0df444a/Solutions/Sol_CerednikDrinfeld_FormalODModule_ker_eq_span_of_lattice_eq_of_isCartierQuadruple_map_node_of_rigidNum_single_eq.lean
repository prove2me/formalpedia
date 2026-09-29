-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_node_of_rigidNum_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d525d666-1a19-5350-9829-eda951ac7428

import Mathlib
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_ker_uZero_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_ker_uOne_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isEtaSection_one_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_node_of_rigidNum_single_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

open scoped Matrix

namespace K83EtaKer

section Std

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

theorem coe_latticeMapEquiv (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : Submodule R (Fin 2 → K)) (v : ↥M) :
    ((latticeMapEquiv g M v : ↥(latticeMap g M)) : Fin 2 → K) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K) := rfl

theorem coe_stdBasisVec (i : Fin 2) :
    ((stdBasisVec (𝒪 := R) K i : ↥(stdFullLattice (𝒪 := R) K).1) : Fin 2 → K) = Pi.single i 1 := rfl

theorem linearIndependent_stdBasisVec (hinj : Function.Injective (algebraMap R K)) :
    LinearIndependent R (stdBasisVec (𝒪 := R) K) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (fun w : ↥(stdFullLattice (𝒪 := R) K).1 => (w : Fin 2 → K) i) hc
  simp only [Submodule.coe_sum, Submodule.coe_smul, coe_stdBasisVec, Finset.sum_apply, Pi.smul_apply,
    Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Submodule.coe_zero, Pi.zero_apply] at h
  rw [Algebra.smul_def, mul_one] at h
  exact hinj (by rw [h, map_zero])

theorem span_stdBasisVec_eq_top :
    Submodule.span R (Set.range (stdBasisVec (𝒪 := R) K)) = ⊤ := by
  rw [← (Submodule.map_injective_of_injective (Submodule.injective_subtype (stdFullLattice (𝒪 := R) K).1)).eq_iff,
    Submodule.map_subtype_top, Submodule.map_span, ← Set.range_comp]
  exact (stdLattice_eq_span R K).symm

noncomputable def stdBasis (hinj : Function.Injective (algebraMap R K)) :
    Module.Basis (Fin 2) R ↥(stdFullLattice (𝒪 := R) K).1 :=
  Module.Basis.mk (linearIndependent_stdBasisVec hinj) (span_stdBasisVec_eq_top (R := R) (K := K)).ge

@[scoped simp] theorem stdBasis_apply (hinj : Function.Injective (algebraMap R K)) (i : Fin 2) :
    stdBasis (K := K) hinj i = stdBasisVec (𝒪 := R) K i :=
  Module.Basis.mk_apply _ _ i

end Std

section Eta

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev pinv : ℚ_[p]ˣ := (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹

noncomputable abbrev Mη (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : FullLattice ℤ_[p] ℚ_[p] :=
  FullLattice.act (scalarGL (pinv p)) (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))

variable (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])

noncomputable def ηequiv (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) :
    ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1 ≃ₗ[ℤ_[p]] ↥M₂.1 :=
  ((latticeMapEquiv g _).trans (latticeMapEquiv (scalarGL (pinv p)) _)).trans (LinearEquiv.ofEq _ _ h)

noncomputable def ηvec (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) (j : Fin 2) : ↥M₂.1 :=
  ηequiv p g M₂ h (stdBasisVec ℚ_[p] j)

theorem coe_ηvec (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) (j : Fin 2) :
    ((ηvec p g M₂ h j : ↥M₂.1) : Fin 2 → ℚ_[p]) =
      ((pinv p : ℚ_[p]ˣ) : ℚ_[p]) • ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ Pi.single j 1) := by
  show ((scalarGL (pinv p) : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ
      ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ Pi.single j 1) = _
  rw [scalarGL_mulVec]

noncomputable def ηbasis (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) : Module.Basis (Fin 2) ℤ_[p] ↥M₂.1 :=
  ((stdBasis (K := ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])).map (ηequiv p g M₂ h)).reindex (Equiv.swap 0 1)

theorem ηbasis_zero (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) :
    ηbasis p g M₂ h 0 = ηvec p g M₂ h 1 := by
  simp [ηbasis, ηvec, Module.Basis.reindex_apply, Equiv.swap_apply_left, Equiv.symm_swap]

theorem ηbasis_one (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) :
    ηbasis p g M₂ h 1 = ηvec p g M₂ h 0 := by
  simp [ηbasis, ηvec, Module.Basis.reindex_apply, Equiv.swap_apply_right, Equiv.symm_swap]

theorem coe_ηbasis_one (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) :
    ((ηbasis p g M₂ h 1 : ↥M₂.1) : Fin 2 → ℚ_[p]) = Pi.single 0 1 := by
  rw [ηbasis_one, coe_ηvec, hg, Matrix.diagonal_mulVec_single, ← Pi.single_smul, smul_eq_mul, Units.val_inv_eq_inv_val,
    unitOfNeZero_coe]
  congr 1
  simp only [Matrix.cons_val_zero, mul_one]
  exact inv_mul_cancel₀ (by rw [map_natCast]; exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

theorem coe_ηbasis_zero (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1) :
    ((ηbasis p g M₂ h 0 : ↥M₂.1) : Fin 2 → ℚ_[p]) = Pi.single 1 ((p : ℚ_[p])⁻¹) := by
  rw [ηbasis_zero, coe_ηvec, hg, Matrix.diagonal_mulVec_single, ← Pi.single_smul, smul_eq_mul, Units.val_inv_eq_inv_val,
    unitOfNeZero_coe]
  congr 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, mul_one]
  rfl

theorem ker_eq_span_transportEquiv_of_ker_eq_span_ηbasis
    {B : Type} [CommRing B] [Algebra ℤ_[p] B]
    (M₂ : FullLattice ℤ_[p] ℚ_[p]) (h : (Mη p g).1 = M₂.1)
    {T : Type} [AddCommGroup T] [Module B T] (u : latticeBaseChange ℤ_[p] ℚ_[p] B M₂ →ₗ[B] T) (c : B)
    (hker : LinearMap.ker u =
      Submodule.span B {c ⊗ₜ[ℤ_[p]] (ηbasis p g M₂ h 0) + (1 : B) ⊗ₜ[ℤ_[p]] (ηbasis p g M₂ h 1)}) :
    LinearMap.ker u = Submodule.span B
      {transportEquiv B
          (M₁ := (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
            (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])))) (M₂ := M₂) h
        (actBaseChange B (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice ℚ_[p]))
          (actBaseChange B g (stdFullLattice ℚ_[p])
            ((1 : B) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} := by
  rw [hker, ηbasis_zero, ηbasis_one]
  congr 2
  simp only [map_add]
  rw [add_comm]
  rfl

end Eta

end K83EtaKer
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_node_of_rigidNum_single_eq.K83EtaKer"

open MvFormalGroup MvFormalGroup.CartierModule

theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
(hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
(X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (γ : Fin 2 → CartierModule p X.F)
(hγ : X.IsHomogeneousVBasis (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) γ)
(hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)

(f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ : f₀.comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) = RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p (WittVector p k ⧸ pIdeal p (WittVector p k))) = 0)
(m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
(hOD₀ : FormalODModule.IsODHom (Rigidified.Φbar (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.Xbar (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))) (Rigidified.ρ (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k))))))))
(hcb : Rigidified.IsGradedSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))))
(a : ℕ)
(hN : ∀ i : Fin 2,
    p ^ a • (Rigidified.rigidNum ι hcΦ rΦ (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) hOD₀ (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k))) hcb hcΦg) (Pi.single i 1) =
      p ^ (a + m) • (![((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 0)))), 0),
          ((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nVarpi (((Rigidified.XbarS (Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))).toGradedCartierModuleData (Rigidified.jSbar ι (Ideal.Quotient.mk (pIdeal p (WittVector p k))) (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) hcb).nMk ((baseChange (reduceMap (RingHom.id (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))) (baseChange f₀ (γ 1)))), 0))] i))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ_[p] Ω] (y₀ : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* Ω)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) Ω)
    (hQ : ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀).IsCartierQuadruple ι hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) Q)
    (x : PrimeSpectrum Ω)
    (h₀ : Q.N₀ x = (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
    (h₁ : Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1) :
        LinearMap.ker (Q.u₀ x) = Submodule.span (locRing Ω x)
          {transportEquiv (locRing Ω x) (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
            ((0 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)} ∧
        LinearMap.ker (Q.u₁ x) = Submodule.span (locRing Ω x)
          {transportEquiv (locRing Ω x)
              (M₁ := FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
                (FullLattice.act g (stdFullLattice ℚ_[p]))) (M₂ := Q.L₁ x) h₁.symm
            (actBaseChange (locRing Ω x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (FullLattice.act g (stdFullLattice ℚ_[p]))
              (actBaseChange (locRing Ω x) g (stdFullLattice ℚ_[p])
                ((1 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : locRing Ω x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} := by
  haveI : CharP Ω p := by
    have h0 : ((p : ℕ) : Ω) = 0 := by
      have h1 : ((p : ℕ) : WittVector p k ⧸ pIdeal p (WittVector p k)) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k)))]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [← map_natCast y₀, h1, map_zero]
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0
  have hx1 : (1 : Ω) ∉ x.asIdeal := (Ideal.ne_top_iff_one _).mp x.isPrime.ne_top
  have hpinv : ((p : ℚ_[p]))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

  obtain ⟨hODΩ, hcΩ, hcbΩ, hcΦΩ, L₀, hL₀, z₀, z₁, hz₀, hz₁, m₀, m₁, hm₀, hm₁, htan₀, hne₀⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isEtaSection_zero_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN Ω y₀
  let e0 : Module.Basis (Fin 2) ℤ_[p] ↥(Q.L₀ x).1 :=
    (K83EtaKer.stdBasis (K := ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])).map
      (LinearEquiv.ofEq _ (Q.L₀ x).1 h₀.symm)
  have he0 : ∀ j : Fin 2, ((e0 j : ↥(Q.L₀ x).1) : Fin 2 → ℚ_[p]) =
      ((stdBasisVec ℚ_[p] j : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]) := fun j => by
    simp only [e0, Module.Basis.map_apply, K83EtaKer.stdBasis_apply]
    rfl
  have hK0 := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.ker_uZero_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
    p k ι Φ hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) Q hQ hODΩ x 1 hx1 hcΩ hcbΩ hcΦΩ L₀ hL₀ e0 z₀ z₁
    (by rw [he0]; exact hz₀) (by rw [he0]; exact hz₁) m₀ m₁ hm₀ hm₁ 0 htan₀ hne₀
  have hv0 : algebraMap Ω (locRing Ω x) 0 ⊗ₜ[ℤ_[p]] (e0 0) + (1 : (locRing Ω x)) ⊗ₜ[ℤ_[p]] (e0 1) =
      transportEquiv (locRing Ω x) (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
        ((0 : (locRing Ω x)) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : (locRing Ω x)) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1) := by
    rw [map_zero, map_add, transportEquiv_tmul, transportEquiv_tmul]
    simp only [e0, Module.Basis.map_apply, K83EtaKer.stdBasis_apply]

  obtain ⟨hODΩ', hcΩ', hcbΩ', hcΦΩ', L₁, hL₁, w₀, w₁, hw₀, hw₁, n₀, n₁, hn₀, hn₁, htan₁, hne₁⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isEtaSection_one_tangent_eq_neg_mul_map_node_of_rigidNum_single_eq
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hrΦ g hg X γ hγ hγa hXs hX4 f₀ hf₀ hf₀ξ hf₀η m ρ₀ hρ₀ hOD₀ hcb hcΦg a hN Ω y₀
  let e1 := K83EtaKer.ηbasis p g (Q.L₁ x) h₁.symm
  have he1₀ : ((e1 0 : ↥(Q.L₁ x).1) : Fin 2 → ℚ_[p]) =
      (p : ℚ_[p])⁻¹ • ((stdBasisVec ℚ_[p] 1 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]) := by
    rw [K83EtaKer.coe_ηbasis_zero p g hg, K83EtaKer.coe_stdBasisVec, ← Pi.single_smul, smul_eq_mul, mul_one]
  have he1₁ : ((e1 1 : ↥(Q.L₁ x).1) : Fin 2 → ℚ_[p]) =
      ((stdBasisVec ℚ_[p] 0 : ↥(stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1) : Fin 2 → ℚ_[p]) := by
    rw [K83EtaKer.coe_ηbasis_one p g hg, K83EtaKer.coe_stdBasisVec]
  have hK1 := CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.ker_uOne_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
    p k ι Φ hcΦ rΦ (y₀.comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) ((Rigidified.mk (Φ := Φ) (X.map f₀) m (ρ₀.map (Ideal.Quotient.mk (pIdeal p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).map y₀) Q hQ hODΩ' x 1 hx1 hcΩ' hcbΩ' hcΦΩ' L₁ hL₁ e1 w₀ w₁
    (by rw [he1₀]; exact hw₀) (by rw [he1₁]; exact hw₁) n₀ n₁ hn₀ hn₁ 0 htan₁ hne₁
  have hK1' := K83EtaKer.ker_eq_span_transportEquiv_of_ker_eq_span_ηbasis p g (Q.L₁ x) h₁.symm (Q.u₁ x) _ hK1
  rw [map_zero] at hK1'
  refine ⟨?_, hK1'⟩
  rw [hK0, hv0]

end S_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_node_of_rigidNum_single_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_ker_eq_span_of_lattice_eq_of_isCartierQuadruple_map_node_of_rigidNum_single_eq (solution)
