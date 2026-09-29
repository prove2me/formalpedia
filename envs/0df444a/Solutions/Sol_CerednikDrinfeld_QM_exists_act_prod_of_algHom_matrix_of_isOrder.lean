-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_act_prod_of_algHom_matrix_of_isOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2d2a5497-3f79-5752-92c1-a8ba130aa021

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

noncomputable section

namespace P2mKcMatrixAct

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct.Pt"

theorem pushPt_natural {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A' ⟶ A') (hφ : φ ≫ f' = f')
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (pushPt φ hφ P) =
      pushPt φ hφ (GoodReductionJacobian.schemeHomOverComp ψ hψ P) :=
  Subtype.ext (Category.assoc _ _ _).symm

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct.Pt"

section Act

variable {L : RelativeGroupLaw R f} [Fact L.IsCommutative]
  {c d : ℚ} {O : Submodule ℤ ℍ[ℚ, c, d]}
  (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
  (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
    pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
  (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
  (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)

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

def Φ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : Pt L t × Pt L t →+ Pt L t × Pt L t :=
  AddMonoidHom.prod
    ((E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 0 0) (hj m 0 0)).coprod (E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 0 1) (hj m 0 1)))
    ((E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 1 0) (hj m 1 0)).coprod (E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 1 1) (hj m 1 1)))

theorem Φ_apply (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : Pt L t × Pt L t) :
    Φ ε hε hε_hom j hj m t x =
      (E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 0 0) (hj m 0 0) x.1 + E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 0 1) (hj m 0 1) x.2,
        E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 1 0) (hj m 1 0) x.1 +
          E ε hε hε_hom (j (m : ℍ[ℚ, a, b]) 1 1) (hj m 1 1) x.2) := by
  simp only [Φ, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply]

def actPt (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)) :
    SchemeHomOver t (prodStr f f) :=
  pair (Φ ε hε hε_hom j hj m t (unpair (L := L) P))

theorem unpair_actPt (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)) :
    unpair (L := L) (actPt ε hε hε_hom j hj m t P) = Φ ε hε hε_hom j hj m t (unpair (L := L) P) := by
  unfold actPt
  rw [unpair_pair]

theorem actPt_natural (m : ↥Λ) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t (prodStr f f)) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (actPt ε hε hε_hom j hj m t P) =
      actPt ε hε hε_hom j hj m t' (GoodReductionJacobian.schemeHomOverComp ψ hψ P) := by
  unfold actPt
  rw [pair_natural, unpair_natural, Φ_apply, Φ_apply]
  congr 1
  refine Prod.ext (Pt.ext ?_) (Pt.ext ?_)
  · simp only [Pt.val_add, val_E]
    rw [L.mul_natural, pushPt_natural, pushPt_natural]
  · simp only [Pt.val_add, val_E]
    rw [L.mul_natural, pushPt_natural, pushPt_natural]

def act (m : ↥Λ) : pullback f f ⟶ pullback f f :=
  (actPt ε hε hε_hom j hj m (prodStr f f) (schemeHomOverId (prodStr f f))).1

theorem act_over (m : ↥Λ) : act ε hε hε_hom j hj m ≫ prodStr f f = prodStr f f :=
  (actPt ε hε hε_hom j hj m (prodStr f f) (schemeHomOverId (prodStr f f))).2

theorem pushPt_act (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)) :
    pushPt (act ε hε hε_hom j hj m) (act_over ε hε hε_hom j hj m) P = actPt ε hε hε_hom j hj m t P := by
  have h1 : pushPt (act ε hε hε_hom j hj m) (act_over ε hε hε_hom j hj m) P =
      GoodReductionJacobian.schemeHomOverComp P.1 P.2
        (actPt ε hε hε_hom j hj m (prodStr f f) (schemeHomOverId (prodStr f f))) :=
    Subtype.ext rfl
  have h2 : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (schemeHomOverId (prodStr f f)) = P :=
    Subtype.ext (Category.comp_id _)
  rw [h1, actPt_natural, h2]

theorem formula (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)) :
    prodFstPt (pushPt (act ε hε hε_hom j hj m) (act_over ε hε hε_hom j hj m) P) =
        L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩) (hε _) (prodFstPt P))
          (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 1, hj m 0 1⟩) (hε _) (prodSndPt P)) ∧
      prodSndPt (pushPt (act ε hε hε_hom j hj m) (act_over ε hε hε_hom j hj m) P) =
        L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 0, hj m 1 0⟩) (hε _) (prodFstPt P))
          (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩) (hε _) (prodSndPt P)) := by
  have h := unpair_actPt ε hε hε_hom j hj m t P
  rw [← pushPt_act, Φ_apply] at h
  have h1 := congrArg (fun x => x.1.val) h
  have h2 := congrArg (fun x => x.2.val) h
  exact ⟨h1, h2⟩

theorem act_hom (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (prodStr f f)) :
    pushPt (act ε hε hε_hom j hj m) (act_over ε hε hε_hom j hj m) ((L.prod L).mul t P Q) =
      (L.prod L).mul t (pushPt (act ε hε hε_hom j hj m) (act_over ε hε hε_hom j hj m) P)
        (pushPt (act ε hε hε_hom j hj m) (act_over ε hε hε_hom j hj m) Q) := by
  rw [pushPt_act, pushPt_act, pushPt_act]
  unfold actPt
  rw [unpair_mul, map_add, pair_add]

section Laws

variable (hO : IsOrder O)
  (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
  (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
    ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
  (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
    pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

include hO hε_one hε_add in

theorem Φ_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Φ ε hε hε_hom j hj ⟨1, h⟩ t = AddMonoidHom.id (Pt L t × Pt L t) := by
  have hj1 : j ((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b]) = 1 := by
    change j 1 = 1
    exact map_one j
  have e00 : (E ε hε hε_hom (j ((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 0 0) (hj ⟨1, h⟩ 0 0) : Pt L t →+ Pt L t) =
      AddMonoidHom.id _ := by
    rw [E_congr ε hε hε_hom (by rw [hj1]; rfl) _ hO.one_mem, E_one ε hε hε_hom hε_one]
  have e11 : (E ε hε hε_hom (j ((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 1 1) (hj ⟨1, h⟩ 1 1) : Pt L t →+ Pt L t) =
      AddMonoidHom.id _ := by
    rw [E_congr ε hε hε_hom (by rw [hj1]; rfl) _ hO.one_mem, E_one ε hε hε_hom hε_one]
  have e01 : (E ε hε hε_hom (j ((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 0 1) (hj ⟨1, h⟩ 0 1) : Pt L t →+ Pt L t) = 0 := by
    rw [E_congr ε hε hε_hom (by rw [hj1]; rfl) _ O.zero_mem, E_zero ε hε hε_hom hε_add]
  have e10 : (E ε hε hε_hom (j ((⟨1, h⟩ : ↥Λ) : ℍ[ℚ, a, b]) 1 0) (hj ⟨1, h⟩ 1 0) : Pt L t →+ Pt L t) = 0 := by
    rw [E_congr ε hε hε_hom (by rw [hj1]; rfl) _ O.zero_mem, E_zero ε hε hε_hom hε_add]
  refine AddMonoidHom.ext fun x => Prod.ext ?_ ?_
  · rw [Φ_apply, e00, e01]
    simp
  · rw [Φ_apply, e10, e11]
    simp

include hO hε_mul hε_add in

theorem E_entry_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) (i l : Fin 2)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (E ε hε hε_hom (j ((⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ : ↥Λ) : ℍ[ℚ, a, b]) i l)
        (hj ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ i l) : Pt L t →+ Pt L t) =
      (E ε hε hε_hom (j (x : ℍ[ℚ, a, b]) i 0) (hj x i 0)).comp (E ε hε hε_hom (j (y : ℍ[ℚ, a, b]) 0 l) (hj y 0 l)) +
        (E ε hε hε_hom (j (x : ℍ[ℚ, a, b]) i 1) (hj x i 1)).comp
          (E ε hε hε_hom (j (y : ℍ[ℚ, a, b]) 1 l) (hj y 1 l)) := by
  have hexp : j ((⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ : ↥Λ) : ℍ[ℚ, a, b]) i l =
      j (x : ℍ[ℚ, a, b]) i 0 * j (y : ℍ[ℚ, a, b]) 0 l + j (x : ℍ[ℚ, a, b]) i 1 * j (y : ℍ[ℚ, a, b]) 1 l := by
    change j ((x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b])) i l = _
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hm0 : j (x : ℍ[ℚ, a, b]) i 0 * j (y : ℍ[ℚ, a, b]) 0 l ∈ O := hO.mul_mem (hj x i 0) (hj y 0 l)
  have hm1 : j (x : ℍ[ℚ, a, b]) i 1 * j (y : ℍ[ℚ, a, b]) 1 l ∈ O := hO.mul_mem (hj x i 1) (hj y 1 l)
  rw [E_congr ε hε hε_hom hexp _ (O.add_mem hm0 hm1), E_add ε hε hε_hom hε_add _ _ hm0 hm1,
    E_mul ε hε hε_hom hε_mul _ _ (hj x i 0) (hj y 0 l), E_mul ε hε hε_hom hε_mul _ _ (hj x i 1) (hj y 1 l)]

include hO hε_mul hε_add in

theorem Φ_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Φ ε hε hε_hom j hj ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ t =
      (Φ ε hε hε_hom j hj x t).comp (Φ ε hε hε_hom j hj y t) := by
  refine AddMonoidHom.ext fun P => Prod.ext ?_ ?_
  · rw [AddMonoidHom.comp_apply, Φ_apply, Φ_apply, Φ_apply]
    dsimp only
    rw [E_entry_mul ε hε hε_hom j hj hO hε_mul hε_add x y h 0 0 t,
      E_entry_mul ε hε hε_hom j hj hO hε_mul hε_add x y h 0 1 t]
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, map_add]
    abel
  · rw [AddMonoidHom.comp_apply, Φ_apply, Φ_apply, Φ_apply]
    dsimp only
    rw [E_entry_mul ε hε hε_hom j hj hO hε_mul hε_add x y h 1 0 t,
      E_entry_mul ε hε hε_hom j hj hO hε_mul hε_add x y h 1 1 t]
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, map_add]
    abel

include hε_add in

theorem E_entry_add (x y : ↥Λ) (i l : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (E ε hε hε_hom (j ((x + y : ↥Λ) : ℍ[ℚ, a, b]) i l) (hj (x + y) i l) : Pt L t →+ Pt L t) =
      E ε hε hε_hom (j (x : ℍ[ℚ, a, b]) i l) (hj x i l) + E ε hε hε_hom (j (y : ℍ[ℚ, a, b]) i l) (hj y i l) := by
  have hexp : j ((x + y : ↥Λ) : ℍ[ℚ, a, b]) i l = j (x : ℍ[ℚ, a, b]) i l + j (y : ℍ[ℚ, a, b]) i l := by
    rw [Submodule.coe_add, map_add, Matrix.add_apply]
  rw [E_congr ε hε hε_hom hexp _ (O.add_mem (hj x i l) (hj y i l)), E_add ε hε hε_hom hε_add _ _ (hj x i l) (hj y i l)]

include hε_add in

theorem Φ_add (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Φ ε hε hε_hom j hj (x + y) t = Φ ε hε hε_hom j hj x t + Φ ε hε hε_hom j hj y t := by
  refine AddMonoidHom.ext fun P => Prod.ext ?_ ?_
  · rw [AddMonoidHom.add_apply, Φ_apply, Φ_apply, Φ_apply]
    dsimp only
    rw [E_entry_add ε hε hε_hom j hj hε_add x y 0 0 t, E_entry_add ε hε hε_hom j hj hε_add x y 0 1 t]
    simp only [AddMonoidHom.add_apply, Prod.fst_add]
    abel
  · rw [AddMonoidHom.add_apply, Φ_apply, Φ_apply, Φ_apply]
    dsimp only
    rw [E_entry_add ε hε hε_hom j hj hε_add x y 1 0 t, E_entry_add ε hε hε_hom j hj hε_add x y 1 1 t]
    simp only [AddMonoidHom.add_apply, Prod.snd_add]
    abel

include hO hε_one hε_add in

theorem act_one (h : (1 : ℍ[ℚ, a, b]) ∈ Λ) : act ε hε hε_hom j hj ⟨1, h⟩ = 𝟙 (pullback f f) := by
  have key : actPt ε hε hε_hom j hj ⟨1, h⟩ (prodStr f f) (schemeHomOverId (prodStr f f)) =
      schemeHomOverId (prodStr f f) := by
    unfold actPt
    rw [Φ_one ε hε hε_hom j hj hO hε_one hε_add h, AddMonoidHom.id_apply, pair_unpair]
  exact congrArg Subtype.val key

include hO hε_mul hε_add in

theorem act_mul (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ) :
    act ε hε hε_hom j hj ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ =
      act ε hε hε_hom j hj y ≫ act ε hε hε_hom j hj x := by

  have key : actPt ε hε hε_hom j hj ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ (prodStr f f)
        (schemeHomOverId (prodStr f f)) =
      actPt ε hε hε_hom j hj x (prodStr f f)
        (actPt ε hε hε_hom j hj y (prodStr f f) (schemeHomOverId (prodStr f f))) := by
    unfold actPt
    rw [Φ_mul ε hε hε_hom j hj hO hε_mul hε_add x y h, AddMonoidHom.comp_apply, unpair_pair]
  have h2 : actPt ε hε hε_hom j hj x (prodStr f f)
        (actPt ε hε hε_hom j hj y (prodStr f f) (schemeHomOverId (prodStr f f))) =
      pushPt (act ε hε hε_hom j hj x) (act_over ε hε hε_hom j hj x)
        (actPt ε hε hε_hom j hj y (prodStr f f) (schemeHomOverId (prodStr f f))) :=
    (pushPt_act ε hε hε_hom j hj x _ _).symm
  rw [h2] at key
  exact congrArg Subtype.val key

include hε_add in

theorem act_add (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)) :
    pushPt (act ε hε hε_hom j hj (x + y)) (act_over ε hε hε_hom j hj (x + y)) P =
      (L.prod L).mul t (pushPt (act ε hε hε_hom j hj x) (act_over ε hε hε_hom j hj x) P)
        (pushPt (act ε hε hε_hom j hj y) (act_over ε hε hε_hom j hj y) P) := by
  rw [pushPt_act, pushPt_act, pushPt_act]
  unfold actPt
  rw [Φ_add ε hε hε_hom j hj hε_add x y t, AddMonoidHom.add_apply, pair_add]

end Laws
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct.Pt"

end Act
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct.Pt"

theorem main
    {R : Type} [CommRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) (hLc : L.IsCommutative)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O) :
    ∃ (act : ↥Λ → (pullback f f ⟶ pullback f f)) (hact : ∀ m : ↥Λ, act m ≫ prodStr f f = prodStr f f),
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        prodFstPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 1, hj m 0 1⟩) (hε _) (prodSndPt P)) ∧
          prodSndPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 0, hj m 1 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩) (hε _) (prodSndPt P))) ∧
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (prodStr f f)),
        pushPt (act m) (hact m) ((L.prod L).mul t P Q) =
          (L.prod L).mul t (pushPt (act m) (hact m) P) (pushPt (act m) (hact m) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 (pullback f f)) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        pushPt (act (x + y)) (hact (x + y)) P =
          (L.prod L).mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P)) := by
  haveI : Fact L.IsCommutative := ⟨hLc⟩
  exact ⟨act ε hε hε_hom j hj, act_over ε hε hε_hom j hj,
    fun m _ t P => formula ε hε hε_hom j hj m t P,
    fun m _ t P Q => act_hom ε hε hε_hom j hj m t P Q,
    fun h => act_one ε hε hε_hom j hj hO hε_one hε_add h,
    fun x y h => act_mul ε hε hε_hom j hj hO hε_mul hε_add x y h,
    fun x y _ t P => act_add ε hε hε_hom j hj hε_add x y t P⟩

end P2mKcMatrixAct
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct.Pt P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct.Pt P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder.P2mKcMatrixAct"

theorem solution
    {R : Type} [CommRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) (hLc : L.IsCommutative)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O) :
    ∃ (act : ↥Λ → (pullback f f ⟶ pullback f f)) (hact : ∀ m : ↥Λ, act m ≫ prodStr f f = prodStr f f),
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        prodFstPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 0 1, hj m 0 1⟩) (hε _) (prodSndPt P)) ∧
          prodSndPt (pushPt (act m) (hact m) P) =
            L.mul t (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 0, hj m 1 0⟩) (hε _) (prodFstPt P))
              (pushPt (ε ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩) (hε _) (prodSndPt P))) ∧
      (∀ (m : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (prodStr f f)),
        pushPt (act m) (hact m) ((L.prod L).mul t P Q) =
          (L.prod L).mul t (pushPt (act m) (hact m) P) (pushPt (act m) (hact m) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 (pullback f f)) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t (prodStr f f)),
        pushPt (act (x + y)) (hact (x + y)) P =
          (L.prod L).mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P)) :=
  P2mKcMatrixAct.main f L hLc O hO ε hε hε_hom hε_one hε_mul hε_add Λ j hj

end S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_isOrder (solution)
