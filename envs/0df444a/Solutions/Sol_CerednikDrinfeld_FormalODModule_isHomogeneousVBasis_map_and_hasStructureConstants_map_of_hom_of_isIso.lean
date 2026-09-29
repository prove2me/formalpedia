-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/46380c60-d62a-54ec-b7d7-99927101a2b0

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso

set_option autoImplicit false

universe u

namespace DDTr
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Matrix

section Generic
variable {q : ℕ} [Fact q.Prime]
variable {B : Type u} [CommRing B] {B' : Type u} [CommRing B']

open MvPowerSeries in
theorem linearPart_comp (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (ψ.comp φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem linearPart_map (f : B →+* B') (φ : Series B) :
    MvFormalGroup.linearPart (φ.map f) = (MvFormalGroup.linearPart φ).map f := by
  ext i j
  simp [MvFormalGroup.linearPart, Series.map, MvPowerSeries.coeff_map]

theorem linearPart_id : MvFormalGroup.linearPart (Series.id B) = 1 := by
  unfold Series.id
  exact MvFormalGroup.linearPart_X

theorem mem_lieZero_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieZero j ↔ ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j a • m := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem mem_lieOne_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieOne j ↔
      ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j (WittVector.frobenius a) • m := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem frob_frob (a : Zp2 q) : WittVector.frobenius (WittVector.frobenius a) = a := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  ext n
  simp only [WittVector.coeff_frobenius_charP]
  rw [← pow_mul, ← pow_two, ← GaloisField.card q 2 two_ne_zero, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem linearPart_varpi_mul_self (X : FormalODModule q B) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart X.varpi =
      ((q : ℕ) : B) • (1 : Matrix (Fin 2) (Fin 2) B) := by
  have h := congrArg MvFormalGroup.linearPart X.varpi_comp_varpi
  rw [linearPart_comp _ _ X.isLawHom_varpi.1, FormalODModule.act_natCast, MvFormalGroup.linearPart_nthSeries] at h
  rw [h]
  ext i i'
  simp [Matrix.smul_apply, nsmul_eq_mul]

theorem linearPart_varpi_mul_act (X : FormalODModule q B) (a : Zp2 q) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (X.act (WittVector.frobenius a)) * MvFormalGroup.linearPart X.varpi := by
  have h := congrArg MvFormalGroup.linearPart (X.varpi_comp_act a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ X.isLawHom_varpi.1] at h

theorem Hom.linearPart_mul_act {X Y : FormalODModule q B} (w : X.Hom Y) (a : Zp2 q) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (Y.act a) * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart (w.isODHom.2.1 a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.linearPart_mul_varpi {X Y : FormalODModule q B} (w : X.Hom Y) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart X.varpi =
      MvFormalGroup.linearPart Y.varpi * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart w.isODHom.2.2
  rwa [linearPart_comp _ _ X.isLawHom_varpi.1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.exists_mul_linearPart_eq_one {X Y : FormalODModule q B} (w : X.Hom Y) (hw : w.IsIso) :
    ∃ W' : Matrix (Fin 2) (Fin 2) B, W' * MvFormalGroup.linearPart w.toSeries = 1 := by
  obtain ⟨g, hg, -⟩ := hw
  refine ⟨MvFormalGroup.linearPart g.toSeries, ?_⟩
  have h := congrArg (fun f : X.Hom X => MvFormalGroup.linearPart f.toSeries) hg
  simp only [FormalODModule.Hom.comp] at h
  rw [linearPart_comp _ _ w.isODHom.1.1] at h
  rw [h]
  exact linearPart_id

theorem Hom.isIso_cast {X X' Y : FormalODModule q B} (h : X = X') (w : X.Hom Y) (hw : w.IsIso) :
    (h ▸ w : X'.Hom Y).IsIso := by
  subst h
  exact hw

end Generic

end DDTr

open DDTr in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X Y : CerednikDrinfeld.FormalODModule p B) (θ : X.Hom Y) (hθ : θ.IsIso)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (a : ℕ → Fin 2 → B) (ha : X.HasStructureConstants γ a) :
    Y.IsHomogeneousVBasis j (fun i => MvFormalGroup.CartierModule.map θ.toLawHom (γ i)) ∧
      Y.HasStructureConstants (fun i => MvFormalGroup.CartierModule.map θ.toLawHom (γ i)) a := by
  classical

  have hact : ∀ c : CerednikDrinfeld.Zp2 p, (Y.actEnd c).comp θ.toLawHom = θ.toLawHom.comp (X.actEnd c) := by
    intro c
    apply MvFormalGroup.Hom.ext
    funext i
    exact (congrFun (θ.isODHom.2.1 c) i).symm
  have hvarpi : Y.varpiEnd.comp θ.toLawHom = θ.toLawHom.comp X.varpiEnd := by
    apply MvFormalGroup.Hom.ext
    funext i
    exact (congrFun θ.isODHom.2.2 i).symm
  have hendAct : ∀ (φX : MvFormalGroup.End X.F) (φY : MvFormalGroup.End Y.F), φY.comp θ.toLawHom = θ.toLawHom.comp φX →
      ∀ f : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.endAct φY (MvFormalGroup.CartierModule.map θ.toLawHom f) =
        MvFormalGroup.CartierModule.map θ.toLawHom (MvFormalGroup.CartierModule.endAct φX f) := by
    intro φX φY h f
    rw [MvFormalGroup.CartierModule.endAct_apply, MvFormalGroup.CartierModule.endAct_apply,
      ← MvFormalGroup.CartierModule.map_comp, h, MvFormalGroup.CartierModule.map_comp]

  have hVit : ∀ (n : ℕ) (f : MvFormalGroup.CartierModule p X.F),
      MvFormalGroup.CartierModule.map θ.toLawHom ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[n] f) =
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Y.F)))^[n] (MvFormalGroup.CartierModule.map θ.toLawHom f) := by
    intro n
    induction n with
    | zero => intro f; rfl
    | succ n ih => intro f; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', MvFormalGroup.CartierModule.map_verschiebungInt, ih]

  obtain ⟨g, hg₁, hg₂⟩ := hθ
  have hgθ : g.toSeries.comp θ.toSeries = CerednikDrinfeld.SpecialFormal.Series.id B := congrArg CerednikDrinfeld.FormalODModule.Hom.toSeries hg₁
  have hlin : MvFormalGroup.linearPart g.toSeries * MvFormalGroup.linearPart θ.toSeries = 1 := by
    have h := congrArg MvFormalGroup.linearPart hgθ

    rwa [linearPart_comp _ _ θ.isODHom.1.1, linearPart_id] at h
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  ·
    rw [CerednikDrinfeld.FormalODModule.mem_gradedPiece_iff]
    intro c
    rw [hendAct _ _ (hact _), (CerednikDrinfeld.FormalODModule.mem_gradedPiece_iff X j i (γ i)).mp (hγ.1 i) c,
      MvFormalGroup.CartierModule.map_homothety]
  ·
    have ht : (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.map θ.toLawHom (γ i)) k) =
        (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (γ i) k) * (MvFormalGroup.linearPart θ.toSeries).transpose := by
      ext i k
      rw [Matrix.of_apply, MvFormalGroup.CartierModule.tangent_map, Matrix.mul_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]; rfl
    rw [ht, Matrix.det_mul, Matrix.det_transpose]
    have hu : IsUnit ((MvFormalGroup.linearPart g.toSeries).det * (MvFormalGroup.linearPart θ.toSeries).det) := by
      rw [← Matrix.det_mul, hlin, Matrix.det_one]; exact isUnit_one
    exact hγ.2.mul (IsUnit.mul_iff.mp hu).2
  ·
    intro i N
    obtain ⟨h, hh⟩ := ha i N
    refine ⟨MvFormalGroup.CartierModule.map θ.toLawHom h, ?_⟩
    rw [hendAct _ _ hvarpi, hh, map_add, map_sum, hVit]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hVit, MvFormalGroup.CartierModule.map_homothety]

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso (solution)
