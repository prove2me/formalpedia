-- Prove2me | solution 1 for CerednikDrinfeld.QM.LatticeAction.table_and_existsUnique_of_table
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/abccc3d4-7d5c-5ba3-9108-98c46af070ad

import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_LatticeAction_table_and_existsUnique_of_table

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

namespace ActDict16

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}
  (L' : RelativeGroupLaw S' f') (hc' : L'.IsCommutative)

theorem pushPt_eq_comp (P : SchemeHomOver f' f') {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S')} (X : SchemeHomOver t f') :
    pushPt P.1 P.2 X = GoodReductionJacobian.schemeHomOverComp X.1 X.2 P := rfl

theorem pushPt_mul (P Q : SchemeHomOver f' f') {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S')} (X : SchemeHomOver t f') :
    pushPt (L'.mul f' P Q).1 (L'.mul f' P Q).2 X = L'.mul t (pushPt P.1 P.2 X) (pushPt Q.1 Q.2 X) := by
  rw [pushPt_eq_comp, pushPt_eq_comp, pushPt_eq_comp]
  exact L'.mul_natural f' t X.1 X.2 P Q

theorem pushPt_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S')} (X : SchemeHomOver t f') :
    pushPt (L'.one f').1 (L'.one f').2 X = L'.one t := by
  rw [pushPt_eq_comp]
  exact L'.one_natural f' t X.1 X.2

theorem pushPt_inv (P : SchemeHomOver f' f') {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S')} (X : SchemeHomOver t f') :
    pushPt (L'.inv f' P).1 (L'.inv f' P).2 X = L'.inv t (pushPt P.1 P.2 X) := by
  letI := L'.pointGroup t
  have h : L'.mul t (pushPt (L'.inv f' P).1 (L'.inv f' P).2 X) (pushPt P.1 P.2 X) = L'.one t := by
    rw [← pushPt_mul, L'.inv_mul_cancel, pushPt_one]
  exact inv_eq_of_mul_eq_one_left h |>.symm

omit L' in

theorem pushPt_idPt (e : A' ⟶ A') (he : e ≫ f' = f') :
    pushPt e he (⟨𝟙 A', Category.id_comp _⟩ : SchemeHomOver f' f') = ⟨e, he⟩ := by
  apply Subtype.ext
  show 𝟙 A' ≫ e = e
  rw [Category.id_comp]

def cmp (P Q : SchemeHomOver f' f') : SchemeHomOver f' f' := ⟨P.1 ≫ Q.1, by rw [Category.assoc, Q.2, P.2]⟩

omit L' in
theorem cmp_coe (P Q : SchemeHomOver f' f') : (cmp P Q).1 = P.1 ≫ Q.1 := rfl

omit L' in
theorem cmp_eq_pushPt (P Q : SchemeHomOver f' f') : cmp P Q = pushPt Q.1 Q.2 P := rfl

def IsHomPt (Q : SchemeHomOver f' f') : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P₁ P₂ : SchemeHomOver t f'),
    pushPt Q.1 Q.2 (L'.mul t P₁ P₂) = L'.mul t (pushPt Q.1 Q.2 P₁) (pushPt Q.1 Q.2 P₂)

theorem IsHomPt.map_one {Q : SchemeHomOver f' f'} (hQ : IsHomPt L' Q) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) :
    pushPt Q.1 Q.2 (L'.one t) = L'.one t := by
  letI := L'.pointGroup t
  have h := hQ t (L'.one t) (L'.one t)
  rw [L'.one_mul] at h

  have : (pushPt Q.1 Q.2 (L'.one t)) * (pushPt Q.1 Q.2 (L'.one t)) = (pushPt Q.1 Q.2 (L'.one t)) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel this

include hc' in
theorem mul_mul_mul_comm' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (a b c d : SchemeHomOver t f') :
    L'.mul t (L'.mul t a b) (L'.mul t c d) = L'.mul t (L'.mul t a c) (L'.mul t b d) := by
  letI := L'.pointCommGroup hc' t
  exact mul_mul_mul_comm a b c d

def homSubgroup : letI := L'.pointCommGroup hc' f'; Subgroup (SchemeHomOver f' f') :=
  letI := L'.pointCommGroup hc' f'
  { carrier := {Q | IsHomPt L' Q}
    one_mem' := by
      intro T t P₁ P₂
      show pushPt (L'.one f').1 (L'.one f').2 _ = L'.mul t (pushPt (L'.one f').1 (L'.one f').2 P₁) (pushPt (L'.one f').1 (L'.one f').2 P₂)
      rw [pushPt_one, pushPt_one, pushPt_one, L'.one_mul]
    mul_mem' := by
      intro P Q hP hQ T t P₁ P₂
      show pushPt (L'.mul f' P Q).1 (L'.mul f' P Q).2 _ = L'.mul t (pushPt (L'.mul f' P Q).1 (L'.mul f' P Q).2 P₁) (pushPt (L'.mul f' P Q).1 (L'.mul f' P Q).2 P₂)
      rw [pushPt_mul, pushPt_mul, pushPt_mul, hP t, hQ t, mul_mul_mul_comm' L' hc']
    inv_mem' := by
      intro P hP T t P₁ P₂
      letI := L'.pointCommGroup hc' t
      show pushPt (L'.inv f' P).1 (L'.inv f' P).2 _ = L'.mul t (pushPt (L'.inv f' P).1 (L'.inv f' P).2 P₁) (pushPt (L'.inv f' P).1 (L'.inv f' P).2 P₂)
      rw [pushPt_inv, pushPt_inv, pushPt_inv, hP t]
      exact mul_inv _ _ }

theorem mem_homSubgroup_iff (Q : SchemeHomOver f' f') : letI := L'.pointCommGroup hc' f'; Q ∈ homSubgroup L' hc' ↔ IsHomPt L' Q := Iff.rfl

theorem isHomPt_id : IsHomPt L' (⟨𝟙 A', Category.id_comp _⟩ : SchemeHomOver f' f') := by
  intro T t P₁ P₂
  have e : ∀ P : SchemeHomOver t f', pushPt (𝟙 A') (Category.id_comp f') P = P := fun P => Subtype.ext (Category.comp_id _)
  rw [e, e, e]

def precompHom (P : SchemeHomOver f' f') : letI := L'.pointCommGroup hc' f'; SchemeHomOver f' f' →* SchemeHomOver f' f' :=
  letI := L'.pointCommGroup hc' f'
  { toFun := fun Q => cmp Q |> fun _ => cmp P Q
    map_one' := by show cmp P (L'.one f') = L'.one f'; rw [cmp_eq_pushPt]; exact pushPt_one L' P
    map_mul' := fun Q₁ Q₂ => by show cmp P (L'.mul f' Q₁ Q₂) = L'.mul f' (cmp P Q₁) (cmp P Q₂); rw [cmp_eq_pushPt, cmp_eq_pushPt, cmp_eq_pushPt]; exact pushPt_mul L' Q₁ Q₂ P }

theorem precompHom_apply (P Q : SchemeHomOver f' f') : letI := L'.pointCommGroup hc' f'; precompHom L' hc' P Q = cmp P Q := rfl

def postcompHom (Q : SchemeHomOver f' f') (hQ : IsHomPt L' Q) : letI := L'.pointCommGroup hc' f'; SchemeHomOver f' f' →* SchemeHomOver f' f' :=
  letI := L'.pointCommGroup hc' f'
  { toFun := fun P => cmp P Q
    map_one' := by show cmp (L'.one f') Q = L'.one f'; rw [cmp_eq_pushPt]; exact hQ.map_one L' f'
    map_mul' := fun P₁ P₂ => by show cmp (L'.mul f' P₁ P₂) Q = L'.mul f' (cmp P₁ Q) (cmp P₂ Q); rw [cmp_eq_pushPt, cmp_eq_pushPt, cmp_eq_pushPt]; exact hQ f' P₁ P₂ }

theorem postcompHom_apply (Q : SchemeHomOver f' f') (hQ : IsHomPt L' Q) (P : SchemeHomOver f' f') : letI := L'.pointCommGroup hc' f'; postcompHom L' hc' Q hQ P = cmp P Q := rfl

def evalHom {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S')} (X : SchemeHomOver t f') :
    letI := L'.pointCommGroup hc' f'; letI := L'.pointCommGroup hc' t; SchemeHomOver f' f' →* SchemeHomOver t f' :=
  letI := L'.pointCommGroup hc' f'; letI := L'.pointCommGroup hc' t
  { toFun := fun P => pushPt P.1 P.2 X
    map_one' := pushPt_one L' X
    map_mul' := fun P Q => pushPt_mul L' P Q X }

theorem evalHom_apply {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S')} (X : SchemeHomOver t f') (P : SchemeHomOver f' f') :
    letI := L'.pointCommGroup hc' f'; letI := L'.pointCommGroup hc' t; evalHom L' hc' X P = pushPt P.1 P.2 X := rfl

end ActDict16

namespace ActDict16

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}
  (L' : RelativeGroupLaw S' f') (hc' : L'.IsCommutative)

def actPt (i' : LatticeAction Λ f' L') (x : ↥Λ) : SchemeHomOver f' f' := ⟨i'.act x, i'.act_over x⟩

theorem actPt_add (i' : LatticeAction Λ f' L') (x y : ↥Λ) :
    letI := L'.pointCommGroup hc' f'; actPt L' i' (x + y) = actPt L' i' x * actPt L' i' y := by
  have h := i'.act_add x y f' ⟨𝟙 A', Category.id_comp _⟩
  rw [pushPt_idPt, pushPt_idPt, pushPt_idPt] at h
  exact h

def actHom (i' : LatticeAction Λ f' L') : letI := L'.pointCommGroup hc' f'; ↥Λ →+ Additive (SchemeHomOver f' f') :=
  letI := L'.pointCommGroup hc' f'
  AddMonoidHom.mk' (fun x => Additive.ofMul (actPt L' i' x)) (fun x y => by
    show Additive.ofMul (actPt L' i' (x + y)) = Additive.ofMul (actPt L' i' x) + Additive.ofMul (actPt L' i' y)
    rw [actPt_add L' hc' i' x y]; rfl)

theorem actPt_sum_zsmul (i' : LatticeAction Λ f' L') {ι : Type} (s : Finset ι) (d : ι → ℤ) (v : ι → ↥Λ) :
    letI := L'.pointCommGroup hc' f'; actPt L' i' (∑ j ∈ s, d j • v j) = ∏ j ∈ s, actPt L' i' (v j) ^ d j := by
  letI := L'.pointCommGroup hc' f'
  have h := map_sum (actHom L' hc' i') (fun j => d j • v j) s
  simp only [map_zsmul] at h
  apply_fun Additive.toMul at h
  rw [toMul_sum] at h
  simp only [toMul_zsmul] at h
  exact h

section coord
variable {n : ℕ} (β : Fin n → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin n → ℤ, x = ∑ j, c j • β j)

noncomputable def coord (x : ↥Λ) : Fin n → ℤ := (hβ x).choose

theorem coord_spec (x : ↥Λ) : x = ∑ j, coord β hβ x j • β j := (hβ x).choose_spec.1

theorem coord_eq_of_eq (x : ↥Λ) (d : Fin n → ℤ) (h : x = ∑ j, d j • β j) : coord β hβ x = d :=
  ((hβ x).unique (coord_spec β hβ x) h)

theorem coord_add (x y : ↥Λ) : coord β hβ (x + y) = coord β hβ x + coord β hβ y := by
  apply coord_eq_of_eq
  conv_lhs => rw [coord_spec β hβ x, coord_spec β hβ y]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.add_apply, add_smul]

theorem coord_basis (j : Fin n) : coord β hβ (β j) = Pi.single j 1 := by
  apply coord_eq_of_eq
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl; simp [hl]
  · intro h; exact absurd (Finset.mem_univ j) h

end coord

theorem zpow_finsum {G : Type*} [CommGroup G] {ι : Type*} (g : G) (d : ι → ℤ) (s : Finset ι) :
    g ^ (∑ i ∈ s, d i) = ∏ i ∈ s, g ^ d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem table_expand {G : Type*} [CommGroup G] {n : ℕ} (E : Fin n → G) (c : Fin n → Fin n → Fin n → ℤ) (x y : Fin n → ℤ) :
    (∏ j, (∏ k, (∏ l, E l ^ c j k l) ^ y k) ^ x j) = ∏ l, E l ^ (∑ j, ∑ k, x j * y k * c j k l) := by
  simp only [← Finset.prod_zpow, ← zpow_mul, zpow_finsum]
  conv_rhs => rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => ?_
  congr 1
  ring

theorem mul_coords {R : Type*} [Ring R] {n : ℕ} (B : Fin n → R) (c : Fin n → Fin n → Fin n → ℤ)
    (hc : ∀ j k, B j * B k = ∑ l, c j k l • B l) (x y : Fin n → ℤ) :
    (∑ j, x j • B j) * (∑ k, y k • B k) = ∑ l, (∑ j, ∑ k, x j * y k * c j k l) • B l := by
  rw [Finset.sum_mul_sum]
  simp_rw [smul_mul_smul_comm, hc, Finset.smul_sum, smul_smul, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]

end ActDict16

open ActDict16 in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ)
    (hc : ∀ j k : Fin (2 * 2), (β j : ℍ[ℚ, a, b]) * (β k : ℍ[ℚ, a, b]) = ∑ l, c j k l • (β l : ℍ[ℚ, a, b]))
    (u : Fin (2 * 2) → ℤ) (hu : (1 : ℍ[ℚ, a, b]) = ∑ l, u l • (β l : ℍ[ℚ, a, b]))
    {S' : Type u} [CommRing S'] {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S')) (L' : RelativeGroupLaw S' f')
    (hc' : L'.IsCommutative) :
    (∀ i' : LatticeAction Λ f' L',
        letI := L'.pointCommGroup hc' f'
        (∀ j k : Fin (2 * 2),
            (∏ l, (⟨i'.act (β l), i'.act_over (β l)⟩ : SchemeHomOver f' f') ^ (c j k l)) =
              ⟨i'.act (β k) ≫ i'.act (β j), by rw [Category.assoc, i'.act_over, i'.act_over]⟩) ∧
        (∏ l, (⟨i'.act (β l), i'.act_over (β l)⟩ : SchemeHomOver f' f') ^ (u l)) = ⟨𝟙 A', Category.id_comp _⟩) ∧
    (∀ (e : Fin (2 * 2) → (A' ⟶ A')) (he : ∀ j, e j ≫ f' = f')
        (hhom : ∀ (j : Fin (2 * 2)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t f'),
          pushPt (e j) (he j) (L'.mul t P Q) = L'.mul t (pushPt (e j) (he j) P) (pushPt (e j) (he j) Q)),
        (letI := L'.pointCommGroup hc' f'
         (∀ j k : Fin (2 * 2), (∏ l, (⟨e l, he l⟩ : SchemeHomOver f' f') ^ (c j k l)) =
            ⟨e k ≫ e j, by rw [Category.assoc, he, he]⟩) ∧
         (∏ l, (⟨e l, he l⟩ : SchemeHomOver f' f') ^ (u l)) = ⟨𝟙 A', Category.id_comp _⟩) →
        ∃! i' : LatticeAction Λ f' L', ∀ j, i'.act (β j) = e j) := by
  classical
  letI instG := L'.pointCommGroup hc' f'

  have hmul : ∀ j k : Fin (2 * 2), (β j : ℍ[ℚ, a, b]) * (β k : ℍ[ℚ, a, b]) ∈ Λ := fun j k => hΛ.mul_mem (β j).2 (β k).2
  have hprodΛ : ∀ j k : Fin (2 * 2), (⟨(β j : ℍ[ℚ, a, b]) * (β k : ℍ[ℚ, a, b]), hmul j k⟩ : ↥Λ) = ∑ l, c j k l • β l := by
    intro j k; apply Subtype.ext
    first
      | (simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]; exact hc j k)
      | (push_cast; simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]; exact hc j k)
      | simpa [Submodule.coe_sum] using hc j k
  have honeΛ : (⟨(1 : ℍ[ℚ, a, b]), hΛ.one_mem⟩ : ↥Λ) = ∑ l, u l • β l := by
    apply Subtype.ext
    first
      | (simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]; exact hu)
      | (push_cast; simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]; exact hu)
      | simpa [Submodule.coe_sum] using hu
  refine ⟨?_, ?_⟩
  ·
    intro i'
    refine ⟨fun j k => ?_, ?_⟩
    · change ∏ l, actPt L' i' (β l) ^ c j k l = _
      rw [← actPt_sum_zsmul L' hc' i' Finset.univ (c j k) β, ← hprodΛ j k]
      apply Subtype.ext
      exact i'.act_mul (β j) (β k) (hmul j k)
    · change ∏ l, actPt L' i' (β l) ^ u l = _
      rw [← actPt_sum_zsmul L' hc' i' Finset.univ u β, ← honeΛ]
      apply Subtype.ext
      exact i'.act_one hΛ.one_mem
  ·
    intro e he hhom htab
    obtain ⟨htab1, htab2⟩ := htab

    let E : Fin (2 * 2) → SchemeHomOver f' f' := fun j => ⟨e j, he j⟩
    have hEhom : ∀ j, IsHomPt L' (E j) := fun j => hhom j
    have hEmem : ∀ j, E j ∈ homSubgroup L' hc' := fun j => (mem_homSubgroup_iff L' hc' _).2 (hEhom j)

    have hx : ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) = ∑ j, coord β hβ x j • (β j : ℍ[ℚ, a, b]) := fun x => by
      have h := congrArg Subtype.val (coord_spec β hβ x)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
      exact h

    let actB : ↥Λ → SchemeHomOver f' f' := fun x => ∏ j, E j ^ coord β hβ x j
    have actB_def : ∀ x, actB x = ∏ j, E j ^ coord β hβ x j := fun x => rfl
    have actB_mem : ∀ x, actB x ∈ homSubgroup L' hc' := fun x =>
      (homSubgroup L' hc').prod_mem fun j _ => (homSubgroup L' hc').zpow_mem (hEmem j) _
    have actB_hom : ∀ x, IsHomPt L' (actB x) := fun x => (mem_homSubgroup_iff L' hc' _).1 (actB_mem x)
    have actB_add : ∀ x y, actB (x + y) = actB x * actB y := fun x y => by
      simp only [actB_def, coord_add β hβ, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
    have actB_basis : ∀ j, actB (β j) = E j := fun j => by
      rw [actB_def, coord_basis β hβ, Finset.prod_eq_single j]
      · simp
      · intro l _ hl; simp [hl]
      · intro h; exact absurd (Finset.mem_univ j) h
    have actB_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, actB ⟨1, h1⟩ = ⟨𝟙 A', Category.id_comp _⟩ := fun h1 => by
      have hcu : coord β hβ ⟨1, h1⟩ = u := coord_eq_of_eq β hβ _ u honeΛ
      rw [actB_def, hcu]
      exact htab2

    have hcmp : ∀ j k, cmp (E k) (E j) = ∏ l, E l ^ c j k l := fun j k => by
      rw [htab1 j k]
      rfl
    have actB_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        actB ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = cmp (actB y) (actB x) := fun x y h => by

      have hco : coord β hβ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ =
          fun l => ∑ j, ∑ k, coord β hβ x j * coord β hβ y k * c j k l := by
        apply coord_eq_of_eq
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
        rw [hx x, hx y]
        exact mul_coords (fun j => (β j : ℍ[ℚ, a, b])) c hc _ _
      rw [actB_def, hco]

      have h1 : cmp (actB y) (actB x) = ∏ j, (cmp (actB y) (E j)) ^ coord β hβ x j := by
        rw [actB_def x, ← precompHom_apply L' hc', map_prod]
        simp only [map_zpow, precompHom_apply]
      have h2 : ∀ j, cmp (actB y) (E j) = ∏ k, (cmp (E k) (E j)) ^ coord β hβ y k := fun j => by
        rw [actB_def y, ← postcompHom_apply L' hc' (E j) (hEhom j), map_prod]
        simp only [map_zpow, postcompHom_apply]
      rw [h1]
      simp only [h2, hcmp]
      exact (table_expand E c _ _).symm

    let I : LatticeAction Λ f' L' :=
      { act := fun x => (actB x).1
        act_over := fun x => (actB x).2
        act_hom := fun x T t P Q => actB_hom x t P Q
        act_one := fun h1 => congrArg Subtype.val (actB_one h1)
        act_mul := fun x y h => by
          show (actB ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩).1 = (actB y).1 ≫ (actB x).1
          rw [actB_mul x y h]
          rfl
        act_add := fun x y T t P => by
          show pushPt (actB (x + y)).1 (actB (x + y)).2 P = L'.mul t (pushPt (actB x).1 (actB x).2 P) (pushPt (actB y).1 (actB y).2 P)
          rw [actB_add]
          exact pushPt_mul L' _ _ P }
    refine ⟨I, fun j => congrArg Subtype.val (actB_basis j), ?_⟩
    intro i'' hi''
    apply LatticeAction.ext
    funext x
    show i''.act x = (actB x).1
    have hpt : actPt L' i'' x = actB x := by
      conv_lhs => rw [coord_spec β hβ x]
      rw [actPt_sum_zsmul L' hc' i'', actB_def]
      refine Finset.prod_congr rfl fun j _ => ?_
      have : actPt L' i'' (β j) = E j := Subtype.ext (hi'' j)
      rw [this]
    exact congrArg Subtype.val hpt

end S_CerednikDrinfeld_QM_LatticeAction_table_and_existsUnique_of_table
end P2MW
export P2MW.S_CerednikDrinfeld_QM_LatticeAction_table_and_existsUnique_of_table (solution)
