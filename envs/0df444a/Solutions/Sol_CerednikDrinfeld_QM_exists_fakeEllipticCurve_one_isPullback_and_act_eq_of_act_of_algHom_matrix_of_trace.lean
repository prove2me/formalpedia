-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1e17dcf0-b5a5-5c62-a392-ef484edcb8ac

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

noncomputable section

namespace P2mExeMatrixAct

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

@[scoped ext] structure Pt (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : Type where

  val : SchemeHomOver t f

namespace Pt

variable (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))

scoped instance : Zero (Pt L t) := ⟨⟨L.one t⟩⟩

scoped instance : Add (Pt L t) := ⟨fun P Q => ⟨L.mul t P.val Q.val⟩⟩

scoped instance : Neg (Pt L t) := ⟨fun P => ⟨L.inv t P.val⟩⟩

scoped instance [Fact L.IsCommutative] : AddCommGroup (Pt L t) where
  add_assoc P Q S := Pt.ext (L.mul_assoc t _ _ _)
  zero_add P := Pt.ext (L.one_mul t _)
  add_zero P := Pt.ext (L.mul_one t _)
  neg_add_cancel P := Pt.ext (L.inv_mul_cancel t _)
  add_comm P Q := Pt.ext (RelativeGroupLaw.IsCommutative.mul_comm (Fact.out (p := L.IsCommutative)) t P.val Q.val)
  nsmul := nsmulRec
  zsmul := zsmulRec

variable {L t}

@[scoped simp] theorem val_add (P Q : Pt L t) : (P + Q).val = L.mul t P.val Q.val := rfl

@[scoped simp] theorem val_zero : (0 : Pt L t).val = L.one t := rfl

end Pt
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt"

theorem pushPt_natural {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A' ⟶ A') (hφ : φ ≫ f' = f')
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (pushPt φ hφ P) =
      pushPt φ hφ (GoodReductionJacobian.schemeHomOverComp ψ hψ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem pushPt_congr_hom {X : Scheme.{0}} {g : X ⟶ Spec (CommRingCat.of R)} {φ φ' : X ⟶ X} (h : φ = φ')
    (hφ : φ ≫ g = g) (hφ' : φ' ≫ g = g) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t g) :
    pushPt φ hφ P = pushPt φ' hφ' P := by
  subst h; rfl

section Entries

variable {L : RelativeGroupLaw R f} [Fact L.IsCommutative]
  {c d : ℚ} {O : Submodule ℤ ℍ[ℚ, c, d]}
  (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
  (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
  {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}

def E (u : ℍ[ℚ, c, d]) (hu : u ∈ O) : Pt L t →+ Pt L t :=
  AddMonoidHom.mk' (fun P => ⟨pushPt (ε ⟨u, hu⟩) (hε _) P.val⟩) fun P Q => Pt.ext (hε_hom ⟨u, hu⟩ t P.val Q.val)

@[scoped simp] theorem val_E (u : ℍ[ℚ, c, d]) (hu : u ∈ O) (P : Pt L t) :
    (E ε hε hε_hom u hu P).val = pushPt (ε ⟨u, hu⟩) (hε _) P.val := rfl

theorem E_congr {u v : ℍ[ℚ, c, d]} (huv : u = v) (hu : u ∈ O) (hv : v ∈ O) :
    (E ε hε hε_hom u hu : Pt L t →+ Pt L t) = E ε hε hε_hom v hv := by
  subst huv; rfl

theorem E_add
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (u v : ℍ[ℚ, c, d]) (hu : u ∈ O) (hv : v ∈ O) (h : u + v ∈ O) :
    (E ε hε hε_hom (u + v) h : Pt L t →+ Pt L t) = E ε hε hε_hom u hu + E ε hε hε_hom v hv := by
  refine AddMonoidHom.ext fun P => Pt.ext ?_
  simp only [val_E, AddMonoidHom.add_apply, Pt.val_add]
  have key := hε_add ⟨u, hu⟩ ⟨v, hv⟩ t P.val
  have hsub : ((⟨u, hu⟩ : ↥O) + ⟨v, hv⟩) = ⟨u + v, h⟩ := Subtype.ext rfl
  rw [hsub] at key
  exact key

theorem E_mul
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (u v : ℍ[ℚ, c, d]) (hu : u ∈ O) (hv : v ∈ O) (h : u * v ∈ O) :
    (E ε hε hε_hom (u * v) h : Pt L t →+ Pt L t) = (E ε hε hε_hom u hu).comp (E ε hε hε_hom v hv) := by
  refine AddMonoidHom.ext fun P => Pt.ext (Subtype.ext ?_)
  simp only [val_E, AddMonoidHom.comp_apply]
  simp only [mapPt_coe]
  rw [hε_mul ⟨u, hu⟩ ⟨v, hv⟩ h, Category.assoc]

theorem E_one (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A) (h : (1 : ℍ[ℚ, c, d]) ∈ O) :
    (E ε hε hε_hom 1 h : Pt L t →+ Pt L t) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun P => Pt.ext (Subtype.ext ?_)
  simp only [val_E, AddMonoidHom.id_apply]
  simp only [mapPt_coe, hε_one h, Category.comp_id]

theorem E_zero
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (h : (0 : ℍ[ℚ, c, d]) ∈ O) :
    (E ε hε hε_hom 0 h : Pt L t →+ Pt L t) = 0 := by
  have h2 := E_add ε hε hε_hom (t := t) hε_add 0 0 h h (by rw [add_zero]; exact h)
  have h3 : (E ε hε hε_hom (0 + 0) (by rw [add_zero]; exact h) : Pt L t →+ Pt L t) = E ε hε hε_hom 0 h :=
    E_congr ε hε hε_hom (add_zero 0) _ _
  rw [h3] at h2
  have h4 : (E ε hε hε_hom 0 h : Pt L t →+ Pt L t) + E ε hε hε_hom 0 h = 0 + E ε hε hε_hom 0 h := by
    rw [zero_add]; exact h2.symm
  exact add_right_cancel h4

end Entries
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt"

section Act

variable {L : RelativeGroupLaw R f} [Fact L.IsCommutative]
  {c d : ℚ} {O : Submodule ℤ ℍ[ℚ, c, d]}
  (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
  (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))

def unpair {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t (prodStr f f)) :
    Pt L t × Pt L t :=
  (⟨prodFstPt P⟩, ⟨prodSndPt P⟩)

def pair {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (x : Pt L t × Pt L t) :
    SchemeHomOver t (prodStr f f) :=
  prodPairPt x.1.val x.2.val

omit [Fact L.IsCommutative] in
@[scoped simp] theorem unpair_pair {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (x : Pt L t × Pt L t) :
    unpair (L := L) (pair x) = x := by
  unfold unpair pair
  rw [prodFstPt_prodPairPt, prodSndPt_prodPairPt]

omit [Fact L.IsCommutative] in
@[scoped simp] theorem pair_unpair {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t (prodStr f f)) :
    pair (unpair (L := L) P) = P :=
  prodPairPt_prodFstPt_prodSndPt P

omit [Fact L.IsCommutative] in
theorem unpair_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (prodStr f f)) :
    unpair (L := L) ((L.prod L).mul t P Q) = unpair (L := L) P + unpair (L := L) Q := by
  unfold unpair
  refine Prod.ext (Pt.ext ?_) (Pt.ext ?_)
  · exact RelativeGroupLaw.prodFstPt_mul L L t P Q
  · exact RelativeGroupLaw.prodSndPt_mul L L t P Q

omit [Fact L.IsCommutative] in
theorem pair_add {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : Pt L t × Pt L t) :
    pair (x + y) = (L.prod L).mul t (pair x) (pair y) := by
  unfold pair
  rw [RelativeGroupLaw.prodPairPt_mul_prodPairPt]
  rfl

omit [Fact L.IsCommutative] in
theorem unpair_natural {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t (prodStr f f)) :
    unpair (L := L) (GoodReductionJacobian.schemeHomOverComp ψ hψ P) =
      (⟨GoodReductionJacobian.schemeHomOverComp ψ hψ (unpair (L := L) P).1.val⟩,
        ⟨GoodReductionJacobian.schemeHomOverComp ψ hψ (unpair (L := L) P).2.val⟩) := by
  unfold unpair
  refine Prod.ext (Pt.ext ?_) (Pt.ext ?_)
  · exact prodFstPt_natural ψ hψ P
  · exact prodSndPt_natural ψ hψ P

omit [Fact L.IsCommutative] in
theorem pair_natural {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : Pt L t × Pt L t) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (pair x) =
      pair (L := L) (⟨GoodReductionJacobian.schemeHomOverComp ψ hψ x.1.val⟩,
        ⟨GoodReductionJacobian.schemeHomOverComp ψ hψ x.2.val⟩) :=
  prodPairPt_natural ψ hψ _ _

def ΦM (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Pt L t × Pt L t →+ Pt L t × Pt L t :=
  AddMonoidHom.prod
    ((E ε hε hε_hom (y 0 0) (hy 0 0)).coprod (E ε hε hε_hom (y 0 1) (hy 0 1)))
    ((E ε hε hε_hom (y 1 0) (hy 1 0)).coprod (E ε hε hε_hom (y 1 1) (hy 1 1)))

theorem ΦM_apply (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : Pt L t × Pt L t) :
    ΦM ε hε hε_hom y hy t x =
      (E ε hε hε_hom (y 0 0) (hy 0 0) x.1 + E ε hε hε_hom (y 0 1) (hy 0 1) x.2,
        E ε hε hε_hom (y 1 0) (hy 1 0) x.1 + E ε hε hε_hom (y 1 1) (hy 1 1) x.2) := by
  simp only [ΦM, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply]

theorem ΦM_congr {y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]} (hyy' : y = y') (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ΦM ε hε hε_hom y hy t = ΦM ε hε hε_hom y' hy' t := by
  subst hyy'; rfl

def actPtM (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t (prodStr f f)) : SchemeHomOver t (prodStr f f) :=
  pair (ΦM ε hε hε_hom y hy t (unpair (L := L) P))

theorem unpair_actPtM (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t (prodStr f f)) :
    unpair (L := L) (actPtM ε hε hε_hom y hy t P) = ΦM ε hε hε_hom y hy t (unpair (L := L) P) := by
  unfold actPtM
  rw [unpair_pair]

theorem actPtM_natural (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t (prodStr f f)) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (actPtM ε hε hε_hom y hy t P) =
      actPtM ε hε hε_hom y hy t' (GoodReductionJacobian.schemeHomOverComp ψ hψ P) := by
  unfold actPtM
  rw [pair_natural, unpair_natural, ΦM_apply, ΦM_apply]
  congr 1
  refine Prod.ext (Pt.ext ?_) (Pt.ext ?_)
  · simp only [Pt.val_add, val_E]
    rw [L.mul_natural, pushPt_natural, pushPt_natural]
  · simp only [Pt.val_add, val_E]
    rw [L.mul_natural, pushPt_natural, pushPt_natural]

def actM (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) : pullback f f ⟶ pullback f f :=
  (actPtM ε hε hε_hom y hy (prodStr f f) (schemeHomOverId (prodStr f f))).1

theorem actM_over (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) : actM ε hε hε_hom y hy ≫ prodStr f f = prodStr f f :=
  (actPtM ε hε hε_hom y hy (prodStr f f) (schemeHomOverId (prodStr f f))).2

theorem actM_congr {y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]} (hyy' : y = y') (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O) :
    actM ε hε hε_hom y hy = actM ε hε hε_hom y' hy' := by
  subst hyy'; rfl

theorem pushPt_actM (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t (prodStr f f)) :
    pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) P = actPtM ε hε hε_hom y hy t P := by
  have h1 : pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) P =
      GoodReductionJacobian.schemeHomOverComp P.1 P.2
        (actPtM ε hε hε_hom y hy (prodStr f f) (schemeHomOverId (prodStr f f))) :=
    Subtype.ext rfl
  have h2 : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (schemeHomOverId (prodStr f f)) = P :=
    Subtype.ext (Category.comp_id _)
  rw [h1, actPtM_natural, h2]

theorem formulaM (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t (prodStr f f)) :
    prodFstPt (pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (prodFstPt P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (prodSndPt P)) ∧
      prodSndPt (pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (prodFstPt P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (prodSndPt P)) := by
  have h := unpair_actPtM ε hε hε_hom y hy t P
  rw [← pushPt_actM, ΦM_apply] at h
  have h1 := congrArg (fun x => x.1.val) h
  have h2 := congrArg (fun x => x.2.val) h
  exact ⟨h1, h2⟩

theorem actM_hom (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P Q : SchemeHomOver t (prodStr f f)) :
    pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) ((L.prod L).mul t P Q) =
      (L.prod L).mul t (pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) P)
        (pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) Q) := by
  rw [pushPt_actM, pushPt_actM, pushPt_actM]
  unfold actPtM
  rw [unpair_mul, map_add, pair_add]

section LawsM

variable (hO : IsOrder O)
  (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
  (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
    ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
  (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
    pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

include hε_one hε_add in

theorem ΦM_one (h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ΦM ε hε hε_hom 1 h1 t = AddMonoidHom.id (Pt L t × Pt L t) := by
  have e00 : (E ε hε hε_hom ((1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) 0 0) (h1 0 0) : Pt L t →+ Pt L t) = AddMonoidHom.id _ := by
    rw [E_congr ε hε hε_hom (Matrix.one_apply_eq 0) _ (by simpa using h1 0 0), E_one ε hε hε_hom hε_one]
  have e11 : (E ε hε hε_hom ((1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) 1 1) (h1 1 1) : Pt L t →+ Pt L t) = AddMonoidHom.id _ := by
    rw [E_congr ε hε hε_hom (Matrix.one_apply_eq 1) _ (by simpa using h1 1 1), E_one ε hε hε_hom hε_one]
  have e01 : (E ε hε hε_hom ((1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) 0 1) (h1 0 1) : Pt L t →+ Pt L t) = 0 := by
    rw [E_congr ε hε hε_hom (Matrix.one_apply_ne (by decide)) _ O.zero_mem, E_zero ε hε hε_hom hε_add]
  have e10 : (E ε hε hε_hom ((1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) 1 0) (h1 1 0) : Pt L t →+ Pt L t) = 0 := by
    rw [E_congr ε hε hε_hom (Matrix.one_apply_ne (by decide)) _ O.zero_mem, E_zero ε hε hε_hom hε_add]
  refine AddMonoidHom.ext fun x => Prod.ext ?_ ?_
  · rw [ΦM_apply, e00, e01]
    simp
  · rw [ΦM_apply, e10, e11]
    simp

include hO hε_mul hε_add in

theorem E_entry_mulM (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
    (h : ∀ i l, (y * y') i l ∈ O) (i l : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (E ε hε hε_hom ((y * y') i l) (h i l) : Pt L t →+ Pt L t) =
      (E ε hε hε_hom (y i 0) (hy i 0)).comp (E ε hε hε_hom (y' 0 l) (hy' 0 l)) +
        (E ε hε hε_hom (y i 1) (hy i 1)).comp (E ε hε hε_hom (y' 1 l) (hy' 1 l)) := by
  have hexp : (y * y') i l = y i 0 * y' 0 l + y i 1 * y' 1 l := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hm0 : y i 0 * y' 0 l ∈ O := hO.mul_mem (hy i 0) (hy' 0 l)
  have hm1 : y i 1 * y' 1 l ∈ O := hO.mul_mem (hy i 1) (hy' 1 l)
  rw [E_congr ε hε hε_hom hexp _ (O.add_mem hm0 hm1), E_add ε hε hε_hom hε_add _ _ hm0 hm1,
    E_mul ε hε hε_hom hε_mul _ _ (hy i 0) (hy' 0 l), E_mul ε hε hε_hom hε_mul _ _ (hy i 1) (hy' 1 l)]

include hO hε_mul hε_add in

theorem ΦM_mul (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
    (h : ∀ i l, (y * y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ΦM ε hε hε_hom (y * y') h t = (ΦM ε hε hε_hom y hy t).comp (ΦM ε hε hε_hom y' hy' t) := by
  refine AddMonoidHom.ext fun P => Prod.ext ?_ ?_
  · rw [AddMonoidHom.comp_apply, ΦM_apply, ΦM_apply, ΦM_apply]
    dsimp only
    rw [E_entry_mulM ε hε hε_hom hO hε_mul hε_add y y' hy hy' h 0 0 t,
      E_entry_mulM ε hε hε_hom hO hε_mul hε_add y y' hy hy' h 0 1 t]
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, map_add]
    abel
  · rw [AddMonoidHom.comp_apply, ΦM_apply, ΦM_apply, ΦM_apply]
    dsimp only
    rw [E_entry_mulM ε hε hε_hom hO hε_mul hε_add y y' hy hy' h 1 0 t,
      E_entry_mulM ε hε hε_hom hO hε_mul hε_add y y' hy hy' h 1 1 t]
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, map_add]
    abel

include hε_add in

theorem E_entry_addM (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
    (h : ∀ i l, (y + y') i l ∈ O) (i l : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (E ε hε hε_hom ((y + y') i l) (h i l) : Pt L t →+ Pt L t) =
      E ε hε hε_hom (y i l) (hy i l) + E ε hε hε_hom (y' i l) (hy' i l) := by
  have hexp : (y + y') i l = y i l + y' i l := Matrix.add_apply y y' i l
  rw [E_congr ε hε hε_hom hexp _ (O.add_mem (hy i l) (hy' i l)), E_add ε hε hε_hom hε_add _ _ (hy i l) (hy' i l)]

include hε_add in

theorem ΦM_add (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
    (h : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ΦM ε hε hε_hom (y + y') h t = ΦM ε hε hε_hom y hy t + ΦM ε hε hε_hom y' hy' t := by
  refine AddMonoidHom.ext fun P => Prod.ext ?_ ?_
  · rw [AddMonoidHom.add_apply, ΦM_apply, ΦM_apply, ΦM_apply]
    dsimp only
    rw [E_entry_addM ε hε hε_hom hε_add y y' hy hy' h 0 0 t, E_entry_addM ε hε hε_hom hε_add y y' hy hy' h 0 1 t]
    simp only [AddMonoidHom.add_apply, Prod.fst_add]
    abel
  · rw [AddMonoidHom.add_apply, ΦM_apply, ΦM_apply, ΦM_apply]
    dsimp only
    rw [E_entry_addM ε hε hε_hom hε_add y y' hy hy' h 1 0 t, E_entry_addM ε hε hε_hom hε_add y y' hy hy' h 1 1 t]
    simp only [AddMonoidHom.add_apply, Prod.snd_add]
    abel

include hε_one hε_add in

theorem actM_one (h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O) : actM ε hε hε_hom 1 h1 = 𝟙 (pullback f f) := by
  have key : actPtM ε hε hε_hom 1 h1 (prodStr f f) (schemeHomOverId (prodStr f f)) =
      schemeHomOverId (prodStr f f) := by
    unfold actPtM
    rw [ΦM_one ε hε hε_hom hε_one hε_add h1, AddMonoidHom.id_apply, pair_unpair]
  exact congrArg Subtype.val key

include hO hε_mul hε_add in

theorem actM_mul (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
    (h : ∀ i l, (y * y') i l ∈ O) :
    actM ε hε hε_hom (y * y') h = actM ε hε hε_hom y' hy' ≫ actM ε hε hε_hom y hy := by

  have key : actPtM ε hε hε_hom (y * y') h (prodStr f f) (schemeHomOverId (prodStr f f)) =
      actPtM ε hε hε_hom y hy (prodStr f f)
        (actPtM ε hε hε_hom y' hy' (prodStr f f) (schemeHomOverId (prodStr f f))) := by
    unfold actPtM
    rw [ΦM_mul ε hε hε_hom hO hε_mul hε_add y y' hy hy' h, AddMonoidHom.comp_apply, unpair_pair]
  have h2 : actPtM ε hε hε_hom y hy (prodStr f f)
        (actPtM ε hε hε_hom y' hy' (prodStr f f) (schemeHomOverId (prodStr f f))) =
      pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy)
        (actPtM ε hε hε_hom y' hy' (prodStr f f) (schemeHomOverId (prodStr f f))) :=
    (pushPt_actM ε hε hε_hom y hy _ _).symm
  rw [h2] at key
  exact congrArg Subtype.val key

include hε_add in

theorem actM_add (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
    (h : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (P : SchemeHomOver t (prodStr f f)) :
    pushPt (actM ε hε hε_hom (y + y') h) (actM_over ε hε hε_hom (y + y') h) P =
      (L.prod L).mul t (pushPt (actM ε hε hε_hom y hy) (actM_over ε hε hε_hom y hy) P)
        (pushPt (actM ε hε hε_hom y' hy') (actM_over ε hε hε_hom y' hy') P) := by
  rw [pushPt_actM, pushPt_actM, pushPt_actM]
  unfold actPtM
  rw [ΦM_add ε hε hε_hom hε_add y y' hy hy' h t, AddMonoidHom.add_apply, pair_add]

end LawsM
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt"

end Act
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt"

end P2mExeMatrixAct
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct"

namespace P2mExeProdEngine

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (hx : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [hx]
    _ = L.one t := L.inv_mul_cancel t x

theorem inv_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : L.inv t (L.one t) = L.one t := by
  have := L.inv_mul_cancel t (L.one t)
  rwa [L.mul_one] at this

theorem nsmulPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    ∀ n : ℕ, nsmulPt L t n (L.one t) = L.one t
  | 0 => rfl
  | n + 1 => by
    show L.mul t (nsmulPt L t n (L.one t)) (L.one t) = L.one t
    rw [nsmulPt_one t n, L.one_mul]

theorem pushPt_one_of_hom (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt φ hφ (L.one t) = L.one t := by
  apply eq_one_of_mul_self
  have h := hhom t (L.one t) (L.one t)
  rw [L.one_mul] at h
  exact h.symm

@[reducible] def unitSection : Spec (CommRingCat.of S) ⟶ A :=
  (L.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem unitSection_comp : unitSection L ≫ f = 𝟙 _ :=
  (L.one (𝟙 (Spec (CommRingCat.of S)))).2

theorem factorsThrough_unitSection_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    FactorsThrough (unitSection L) P ↔ P = L.one t := by
  have hnat : (L.one t).1 = t ≫ unitSection L := by
    have := L.one_natural (𝟙 (Spec (CommRingCat.of S))) t t (Category.comp_id t)
    rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]
  constructor
  · rintro ⟨P₀, hP₀⟩
    have hP₀t : P₀ = t := by
      have := congrArg (· ≫ f) hP₀
      simp only [Category.assoc, unitSection_comp, Category.comp_id] at this
      rw [this, P.2]
    apply Subtype.ext
    rw [hnat, ← hP₀, hP₀t]
  · rintro rfl
    exact ⟨t, hnat.symm⟩

theorem topologicalKrullDim_fibre_eq {K : Type} [Field K] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n g] (e : Spec (CommRingCat.of K) ⟶ X) (s : ↥(Spec (CommRingCat.of K))) :
    topologicalKrullDim ↥(g.base ⁻¹' {s}) = n := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have huniv : g.base ⁻¹' {s} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph]
  haveI : Nonempty X := ⟨e.base (IsLocalRing.closedPoint K)⟩
  exact le_antisymm (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le g n)
    (AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim g n)

end P2mExeProdEngine
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct"

namespace P2mExeAssembly

open P2mExeMatrixAct P2mExeProdEngine

theorem smooth2 {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA1 : SmoothOfRelativeDimension 1 f) : SmoothOfRelativeDimension 2 (prodStr f f) := by
  haveI : SmoothOfRelativeDimension 1 f := hA1
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 1) f f hA1
  exact inferInstanceAs (SmoothOfRelativeDimension (1 + 1) (pullback.fst f f ≫ f))

def witness
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hLc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (hA1 : SmoothOfRelativeDimension 1 f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (hj_trace : ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F),
      (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
      (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
      (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
        χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F)) :
    FakeEllipticCurve Λ 1 k :=
  haveI : Fact L.IsCommutative := ⟨hLc⟩
  haveI : SmoothOfRelativeDimension 2 (prodStr f f) := smooth2 f hA1
  have hbundle : AbelianSchemePropertyBundle k (prodStr f f) := GoodReductionJacobian.abelianSchemePropertyBundle_prodStr hA hA
  { A := pullback f f
    f := prodStr f f
    L := L.prod L
    comm := RelativeGroupLaw.IsCommutative.prod hLc hLc
    bundle := hbundle
    dim_fibre := fun s => topologicalKrullDim_fibre_eq (prodStr f f) 2 (unitSection (L.prod L)) s
    act := fun m => actM ε hε hε_hom (j (m : ℍ[ℚ, a, b])) (hj m)
    act_over := fun m => actM_over ε hε hε_hom (j (m : ℍ[ℚ, a, b])) (hj m)
    act_hom := fun m _ t P Q => actM_hom ε hε hε_hom (j (m : ℍ[ℚ, a, b])) (hj m) t P Q
    act_one := fun h => by
      have h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O := fun i l => by
        have := hj ⟨1, h⟩ i l
        rwa [show j (((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b])) = 1 from map_one j] at this
      rw [actM_congr ε hε hε_hom (show j (((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b])) = 1 from map_one j) _ h1]
      exact actM_one ε hε hε_hom hε_one hε_add h1
    act_mul := fun x y h => by
      have hxy : j ((⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ : ↥Λ) : ℍ[ℚ, a, b]) =
          j (x : ℍ[ℚ, a, b]) * j (y : ℍ[ℚ, a, b]) := map_mul j _ _
      have hm : ∀ i l, (j (x : ℍ[ℚ, a, b]) * j (y : ℍ[ℚ, a, b])) i l ∈ O := fun i l => by
        have := hj ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ i l
        rwa [hxy] at this
      rw [actM_congr ε hε hε_hom hxy _ hm]
      exact actM_mul ε hε hε_hom hO hε_mul hε_add _ _ (hj x) (hj y) hm
    act_add := fun x y _ t P => by
      have hxy : j (((x + y : ↥Λ)) : ℍ[ℚ, a, b]) = j (x : ℍ[ℚ, a, b]) + j (y : ℍ[ℚ, a, b]) := by
        rw [Submodule.coe_add, map_add]
      have hm : ∀ i l, (j (x : ℍ[ℚ, a, b]) + j (y : ℍ[ℚ, a, b])) i l ∈ O := fun i l => by
        have := hj (x + y) i l
        rwa [hxy] at this
      rw [pushPt_congr_hom (actM_congr ε hε hε_hom hxy (hj (x + y)) hm)]
      exact actM_add ε hε hε_hom hε_add _ _ (hj x) (hj y) hm t P
    act_trace := by
      intro k' _ _ sk V _ _ _ τ hinj hrange hτadd hτsmul m Φ hΦ n hn
      exact CerednikDrinfeld.QM.trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one q k f L hLc
        hA1 O hO ε hε hε_hom hε_one hε_mul hε_add Λ j hj hj_trace m (actM ε hε hε_hom (j (m : ℍ[ℚ, a, b])) (hj m))
        (actM_over ε hε hε_hom (j (m : ℍ[ℚ, a, b])) (hj m))
        (fun t P => formulaM ε hε hε_hom (j (m : ℍ[ℚ, a, b])) (hj m) t P)
        k' sk V τ hinj hrange hτadd hτsmul Φ hΦ n hn
    C := Spec (CommRingCat.of k)
    lev := unitSection (L.prod L)
    lev_closed := by
      haveI : IsProper (prodStr f f) := hbundle.proper
      haveI : IsClosedImmersion (unitSection (L.prod L) ≫ prodStr f f) := by
        rw [unitSection_comp]; infer_instance
      exact IsClosedImmersion.of_comp (unitSection (L.prod L)) (prodStr f f)
    lev_sub := by
      intro T t P Q hP hQ
      rw [factorsThrough_unitSection_iff] at hP hQ ⊢
      rw [factorsThrough_unitSection_iff]
      subst hP; subst hQ
      exact ⟨(L.prod L).one_mul t _, inv_one (L.prod L) t⟩
    lev_one := fun t => (factorsThrough_unitSection_iff (L.prod L) t _).2 rfl
    lev_torsion := by
      intro T t P hP
      rw [factorsThrough_unitSection_iff] at hP
      subst hP
      exact nsmulPt_one (L.prod L) t 1
    lev_stable := by
      intro x T t P hP
      rw [factorsThrough_unitSection_iff] at hP ⊢
      subst hP
      exact pushPt_one_of_hom (L.prod L) _ (actM_over ε hε hε_hom (j (x : ℍ[ℚ, a, b])) (hj x))
        (fun t P Q => actM_hom ε hε hε_hom (j (x : ℍ[ℚ, a, b])) (hj x) t P Q) t
    lev_finite := by rw [unitSection_comp]; infer_instance
    lev_flat := by rw [unitSection_comp]; infer_instance
    lev_finitePresentation := by rw [unitSection_comp]; infer_instance
    lev_rank := by
      intro s
      rw [unitSection_comp, Scheme.Hom.finrank_eq_one_of_isIso]
      simp
    lev_fibre := by
      intro k' _ _ sk _
      haveI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff).2 rfl
      haveI : Unique (ZMod 1 × ZMod 1) := uniqueOfSubsingleton (0, 0)
      haveI : Unique {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection (L.prod L)) P} :=
        { default := ⟨(L.prod L).one _, (factorsThrough_unitSection_iff (L.prod L) _ _).2 rfl⟩
          uniq := fun P => Subtype.ext ((factorsThrough_unitSection_iff (L.prod L) _ _).1 P.2) }
      refine ⟨Equiv.ofUnique _ _, fun x y => ?_⟩
      have h1 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ (x + y) :
          {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection (L.prod L)) P}) :
            SchemeHomOver (geomPoint k' sk) (prodStr f f)) = (L.prod L).one _ :=
        (factorsThrough_unitSection_iff (L.prod L) _ _).1 (Subtype.prop _)
      have h2 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ x :
          {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection (L.prod L)) P}) :
            SchemeHomOver (geomPoint k' sk) (prodStr f f)) = (L.prod L).one _ :=
        (factorsThrough_unitSection_iff (L.prod L) _ _).1 (Subtype.prop _)
      have h3 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ y :
          {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection (L.prod L)) P}) :
            SchemeHomOver (geomPoint k' sk) (prodStr f f)) = (L.prod L).one _ :=
        (factorsThrough_unitSection_iff (L.prod L) _ _).1 (Subtype.prop _)
      rw [h1, h2, h3, (L.prod L).one_mul] }

end P2mExeAssembly
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct.Pt P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace.P2mExeMatrixAct"

open P2mExeMatrixAct P2mExeProdEngine P2mExeAssembly in

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hLc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (hA1 : SmoothOfRelativeDimension 1 f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (hj_trace : ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F),
      (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
      (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
      (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
        χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F)) :
    ∃ (A₀ : FakeEllipticCurve Λ 1 k) (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f)
      (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
      (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f),

      CategoryTheory.IsPullback p₁ p₂ f f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
        mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
        mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P))) ∧

      (∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A₀.f),
        pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q)) ∧
      (∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A₀.f),
        pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P)) := by
  haveI : Fact L.IsCommutative := ⟨hLc⟩
  refine ⟨witness q k f L hLc hA hA1 O hO ε hε hε_hom hε_one hε_mul hε_add Λ hΛ j hj hj_trace,
    pullback.fst f f, pullback.snd f f, rfl, pullback_snd_comp_eq_prodStr f f,
    fun y hy => actM ε hε hε_hom y hy, fun y hy => actM_over ε hε hε_hom y hy,
    IsPullback.of_hasPullback f f, ?_, ?_, fun m => rfl, ?_, ?_, ?_, ?_⟩
  ·
    intro T t P Q
    exact ⟨RelativeGroupLaw.prodFstPt_mul L L t P Q, RelativeGroupLaw.prodSndPt_mul L L t P Q⟩
  ·
    intro y hy T t P
    exact formulaM ε hε hε_hom y hy t P
  ·
    intro y hy T t P Q
    exact actM_hom ε hε hε_hom y hy t P Q
  ·
    intro h1
    exact actM_one ε hε hε_hom hε_one hε_add h1
  ·
    intro y y' hy hy' hyy'
    exact actM_mul ε hε hε_hom hO hε_mul hε_add y y' hy hy' hyy'
  ·
    intro y y' hy hy' hyy' T t P
    exact actM_add ε hε hε_hom hε_add y y' hy hy' hyy' t P

end S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_fakeEllipticCurve_one_isPullback_and_act_eq_of_act_of_algHom_matrix_of_trace (solution)
