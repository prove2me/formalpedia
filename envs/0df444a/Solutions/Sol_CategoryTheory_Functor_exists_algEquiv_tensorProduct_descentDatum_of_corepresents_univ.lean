-- Prove2me | solution 1 for CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b45a39df-d027-58f0-af77-aa6238559aec

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct Algebra.TensorProduct

universe u v

namespace DatumFromFunctor

variable {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
  (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
  (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]

abbrev ob (B : Type u) [CommRing B] [Algebra R B] : Under (CommRingCat.of R) :=
  Under.mk (CommRingCat.ofHom (algebraMap R B))

abbrev hm {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ψ : B →ₐ[R] B') :
    ob (R := R) B ⟶ ob B' :=
  Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by ext r; exact ψ.commutes r)

theorem hm_comp {B B' B'' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] [CommRing B''] [Algebra R B'']
    (ψ : B →ₐ[R] B') (ψ' : B' →ₐ[R] B'') : hm (R := R) (ψ'.comp ψ) = hm ψ ≫ hm ψ' := by
  ext; rfl

theorem map_comp_apply {B B' B'' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] [CommRing B'']
    [Algebra R B''] (ψ : B →ₐ[R] B') (ψ' : B' →ₐ[R] B'') (x : F.obj (ob B)) :
    F.map (hm (ψ'.comp ψ)) x = F.map (hm ψ') (F.map (hm ψ) x) := by
  rw [hm_comp, F.map_comp]; rfl

theorem map_id_apply {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (ob B)) :
    F.map (hm (AlgHom.id R B)) x = x := by
  have : hm (R := R) (AlgHom.id R B) = 𝟙 _ := by ext; rfl
  rw [this, F.map_id]; rfl

variable (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})

def Natural : Prop :=
  ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1

variable (he : Natural F S₁ C₁ e)

local notation "ι" => IsScalarTower.toAlgHom R S₁ C₁

include he in

theorem nat {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (ob B)) (j' : S₁ →ₐ[R] B') (hj' : ψ.comp j = j') :
    ((e B' j') (F.map (hm ψ) x)).1 = ψ.comp ((e B j) x).1 := by
  subst hj'; exact he B B' j ψ x

noncomputable def xu : F.obj (ob (R := R) C₁) := (e C₁ ι).symm ⟨AlgHom.id R C₁, AlgHom.id_comp _⟩

theorem e_xu : ((e C₁ ι) (xu F S₁ C₁ e)).1 = AlgHom.id R C₁ := by
  simp [xu]

include he in

theorem eq_map_xu {B : Type u} [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B) (x : F.obj (ob B)) :
    x = F.map (hm ((e B j x).1)) (xu F S₁ C₁ e) := by
  apply (e B j).injective
  apply Subtype.ext
  rw [nat F S₁ C₁ e he ι ((e B j x).1) (xu F S₁ C₁ e) j ((e B j x).2), e_xu, AlgHom.comp_id]

noncomputable def x₀ : F.obj (ob (R := R) (S₁ ⊗[R] C₁)) :=
  F.map (hm (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)) (xu F S₁ C₁ e)

noncomputable def g₀ : C₁ →ₐ[R] S₁ ⊗[R] C₁ :=
  ((e (S₁ ⊗[R] C₁) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)) (x₀ F S₁ C₁ e)).1

theorem g₀_comp_ι : (g₀ F S₁ C₁ e).comp ι = includeLeft :=
  ((e (S₁ ⊗[R] C₁) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)) (x₀ F S₁ C₁ e)).2

include he in
theorem e_x₀_right : ((e (S₁ ⊗[R] C₁) ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι)) (x₀ F S₁ C₁ e)).1 =
    includeRight := by
  have := nat F S₁ C₁ e he ι (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) (xu F S₁ C₁ e)
    ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι) rfl
  rw [e_xu, AlgHom.comp_id] at this
  exact this

include he in

theorem core {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj (ob D)) :
    ((e D j₁) x).1 = (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)).comp (g₀ F S₁ C₁ e) := by
  have hθR : (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)).comp includeRight = ((e D j₂) x).1 :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
  have hθL : (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)).comp includeLeft = j₁ :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

  have hx : F.map (hm (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _))) (x₀ F S₁ C₁ e) = x := by
    rw [x₀, ← map_comp_apply, hθR]
    exact (eq_map_xu F S₁ C₁ e he j₂ x).symm
  have key := nat F S₁ C₁ e he (B := S₁ ⊗[R] C₁) (B' := D) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)
    (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)) (x₀ F S₁ C₁ e) j₁ hθL
  rw [hx] at key
  rw [key, g₀]

noncomputable def φ₀ : C₁ ⊗[R] S₁ →ₐ[R] S₁ ⊗[R] C₁ :=
  Algebra.TensorProduct.lift (g₀ F S₁ C₁ e) ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι) (fun _ _ => Commute.all _ _)

theorem φ₀_tmul (c : C₁) (s : S₁) : φ₀ F S₁ C₁ e (c ⊗ₜ[R] s) = g₀ F S₁ C₁ e c * ((1 : S₁) ⊗ₜ[R] (ι s)) := by
  simp [φ₀, Algebra.TensorProduct.lift_tmul]

theorem g₀_ι (s : S₁) : g₀ F S₁ C₁ e (ι s) = s ⊗ₜ[R] (1 : C₁) := by
  have := AlgHom.congr_fun (g₀_comp_ι F S₁ C₁ e) s
  simpa using this

include he in

theorem intertwine {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj (ob D)) :
    Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _)).comp (φ₀ F S₁ C₁ e) := by
  have hc := core F S₁ C₁ e he j₁ j₂ x
  have hg₂ι : ((e D j₂) x).1.comp ι = j₂ := ((e D j₂) x).2
  apply Algebra.TensorProduct.ext'
  intro c s
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, φ₀_tmul, map_mul, Algebra.TensorProduct.lift_tmul,
    map_one, one_mul]
  congr 1
  · exact AlgHom.congr_fun hc c
  · exact (AlgHom.congr_fun hg₂ι s).symm

theorem φ₀_linear :
    (φ₀ F S₁ C₁ e).comp (Algebra.TensorProduct.map ι (AlgHom.id R S₁)) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) ι := by
  apply Algebra.TensorProduct.ext'
  intro s s'
  rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, φ₀_tmul, g₀_ι]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

noncomputable def x₁ : F.obj (ob (R := R) (C₁ ⊗[R] S₁)) :=
  F.map (hm (includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁)) (xu F S₁ C₁ e)

noncomputable def h₀ : C₁ →ₐ[R] C₁ ⊗[R] S₁ :=
  ((e (C₁ ⊗[R] S₁) (includeRight : S₁ →ₐ[R] C₁ ⊗[R] S₁)) (x₁ F S₁ C₁ e)).1

theorem h₀_comp_ι : (h₀ F S₁ C₁ e).comp ι = includeRight :=
  ((e (C₁ ⊗[R] S₁) (includeRight : S₁ →ₐ[R] C₁ ⊗[R] S₁)) (x₁ F S₁ C₁ e)).2

include he in
theorem e_x₁_left : ((e (C₁ ⊗[R] S₁) ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι)) (x₁ F S₁ C₁ e)).1 =
    includeLeft := by
  have := nat F S₁ C₁ e he ι (includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁) (xu F S₁ C₁ e)
    ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι) rfl
  rw [e_xu, AlgHom.comp_id] at this
  exact this

include he in

theorem core' {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj (ob D)) :
    ((e D j₂) x).1 = (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)).comp (h₀ F S₁ C₁ e) := by
  have hθL : (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)).comp includeLeft = ((e D j₁) x).1 :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
  have hθR : (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)).comp includeRight = j₂ :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
  have hx : F.map (hm (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _))) (x₁ F S₁ C₁ e) = x := by
    rw [x₁, ← map_comp_apply, hθL]
    exact (eq_map_xu F S₁ C₁ e he j₁ x).symm
  have key := nat F S₁ C₁ e he (B := C₁ ⊗[R] S₁) (B' := D) (includeRight : S₁ →ₐ[R] C₁ ⊗[R] S₁)
    (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)) (x₁ F S₁ C₁ e) j₂ hθR
  rw [hx] at key
  rw [key, h₀]

noncomputable def ψ₀ : S₁ ⊗[R] C₁ →ₐ[R] C₁ ⊗[R] S₁ :=
  Algebra.TensorProduct.lift ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι) (h₀ F S₁ C₁ e) (fun _ _ => Commute.all _ _)

theorem ψ₀_tmul (s : S₁) (c : C₁) : ψ₀ F S₁ C₁ e (s ⊗ₜ[R] c) = ((ι s) ⊗ₜ[R] (1 : S₁)) * h₀ F S₁ C₁ e c := by
  simp [ψ₀, Algebra.TensorProduct.lift_tmul]

include he in

theorem intertwine' {D : Type u} [CommRing D] [Algebra R D] (j₁ j₂ : S₁ →ₐ[R] D) (x : F.obj (ob D)) :
    Algebra.TensorProduct.lift j₁ ((e D j₂) x).1 (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.lift ((e D j₁) x).1 j₂ (fun _ _ => Commute.all _ _)).comp (ψ₀ F S₁ C₁ e) := by
  have hc := core' F S₁ C₁ e he j₁ j₂ x
  have hg₁ι : ((e D j₁) x).1.comp ι = j₁ := ((e D j₁) x).2
  apply Algebra.TensorProduct.ext'
  intro s c
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, ψ₀_tmul, map_mul, Algebra.TensorProduct.lift_tmul,
    map_one, mul_one]
  congr 1
  · exact (AlgHom.congr_fun hg₁ι s).symm
  · exact AlgHom.congr_fun hc c

include he in
theorem ψ₀_comp_φ₀ : (ψ₀ F S₁ C₁ e).comp (φ₀ F S₁ C₁ e) = AlgHom.id R (C₁ ⊗[R] S₁) := by
  have h := intertwine F S₁ C₁ e he ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι) includeRight (x₁ F S₁ C₁ e)
  have h1 : ((e (C₁ ⊗[R] S₁) ((includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁).comp ι)) (x₁ F S₁ C₁ e)).1 = includeLeft :=
    e_x₁_left F S₁ C₁ e he
  rw [h1] at h
  rw [Algebra.TensorProduct.lift_includeLeft_includeRight] at h
  exact h.symm

include he in
theorem φ₀_comp_ψ₀ : (φ₀ F S₁ C₁ e).comp (ψ₀ F S₁ C₁ e) = AlgHom.id R (S₁ ⊗[R] C₁) := by
  have h := intertwine' F S₁ C₁ e he includeLeft ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι) (x₀ F S₁ C₁ e)
  have h2 : ((e (S₁ ⊗[R] C₁) ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι)) (x₀ F S₁ C₁ e)).1 = includeRight :=
    e_x₀_right F S₁ C₁ e he
  rw [h2] at h
  rw [Algebra.TensorProduct.lift_includeLeft_includeRight] at h
  exact h.symm

noncomputable def φ (he : Natural F S₁ C₁ e) : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁ :=
  AlgEquiv.ofAlgHom (φ₀ F S₁ C₁ e) (ψ₀ F S₁ C₁ e) (φ₀_comp_ψ₀ F S₁ C₁ e he) (ψ₀_comp_φ₀ F S₁ C₁ e he)

theorem φ_toAlgHom (he : Natural F S₁ C₁ e) : (φ F S₁ C₁ e he).toAlgHom = φ₀ F S₁ C₁ e := rfl

theorem lift_includeLeft_includeRight_comp {Y : Type u} [CommRing Y] [Algebra R Y] (f : C₁ →ₐ[R] Y) :
    Algebra.TensorProduct.lift (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] Y) ((includeRight : Y →ₐ[R] S₁ ⊗[R] Y).comp f)
      (fun _ _ => Commute.all _ _) = Algebra.TensorProduct.map (AlgHom.id R S₁) f := by
  apply Algebra.TensorProduct.ext'
  intro s c
  simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

include he in

theorem coact (c : C₁) :
    Algebra.TensorProduct.map (AlgHom.id R S₁) (g₀ F S₁ C₁ e) (g₀ F S₁ C₁ e c) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) (g₀ F S₁ C₁ e c) := by
  let D₂ : Type u := S₁ ⊗[R] (S₁ ⊗[R] C₁)
  let inR₂ : S₁ ⊗[R] C₁ →ₐ[R] D₂ := includeRight
  let k₁ : S₁ →ₐ[R] D₂ := inR₂.comp (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁)
  let k₂ : S₁ →ₐ[R] D₂ := inR₂.comp ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι)
  let k₀ : S₁ →ₐ[R] D₂ := includeLeft
  let x₂ : F.obj (ob D₂) := F.map (hm (B := S₁ ⊗[R] C₁) (B' := D₂) inR₂) (x₀ F S₁ C₁ e)
  have e1 : ((e D₂ k₁) x₂).1 = inR₂.comp (g₀ F S₁ C₁ e) :=
    nat F S₁ C₁ e he (B := S₁ ⊗[R] C₁) (B' := D₂) (includeLeft : S₁ →ₐ[R] S₁ ⊗[R] C₁) inR₂ (x₀ F S₁ C₁ e) k₁ rfl
  have e2 : ((e D₂ k₂) x₂).1 = inR₂.comp includeRight := by
    have := nat F S₁ C₁ e he (B := S₁ ⊗[R] C₁) (B' := D₂) ((includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁).comp ι) inR₂
      (x₀ F S₁ C₁ e) k₂ rfl
    rw [e_x₀_right F S₁ C₁ e he] at this
    exact this
  have c1 := core F S₁ C₁ e he (D := D₂) k₀ k₁ x₂
  have c2 := core F S₁ C₁ e he (D := D₂) k₀ k₂ x₂
  rw [e1, lift_includeLeft_includeRight_comp] at c1
  rw [e2, lift_includeLeft_includeRight_comp] at c2
  have := AlgHom.congr_fun (c1.symm.trans c2) c
  simpa only [AlgHom.comp_apply] using this

theorem assoc_left (y : S₁ ⊗[R] C₁) :
    Algebra.TensorProduct.map (AlgHom.id R S₁) (φ₀ F S₁ C₁ e)
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁) (y ⊗ₜ[R] (1 : S₁))) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) (g₀ F S₁ C₁ e) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, φ₀_tmul,
      map_one, AlgHom.id_apply, show ((1 : S₁) ⊗ₜ[R] (1 : C₁)) = (1 : S₁ ⊗[R] C₁) from rfl, mul_one]
  | add y₁ y₂ h₁ h₂ => simp only [add_tmul, map_add, h₁, h₂]

theorem assoc_right (y : S₁ ⊗[R] C₁) :
    Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁) (y ⊗ₜ[R] (1 : S₁))) =
      Algebra.TensorProduct.map (AlgHom.id R S₁) (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    simp [Algebra.TensorProduct.comm_tmul]
  | add y₁ y₂ h₁ h₂ => simp only [add_tmul, map_add, h₁, h₂]

include he in

theorem cocycle :
    (Algebra.TensorProduct.map (AlgHom.id R S₁) (φ₀ F S₁ C₁ e)).comp
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
          (Algebra.TensorProduct.map (φ₀ F S₁ C₁ e) (AlgHom.id R S₁))) =
      (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom).comp
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
          ((Algebra.TensorProduct.map (φ₀ F S₁ C₁ e) (AlgHom.id R S₁)).comp
            ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁ S₁).toAlgHom).comp
                (Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).toAlgHom)))) := by
  apply Algebra.TensorProduct.ext'
  intro p s'
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [add_tmul, map_add, hp, hq]
  | tmul c s =>

    have L : (Algebra.TensorProduct.map (AlgHom.id R S₁) (φ₀ F S₁ C₁ e))
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁) ((φ₀ F S₁ C₁ e (c ⊗ₜ[R] s)) ⊗ₜ[R] s')) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (g₀ F S₁ C₁ e) (g₀ F S₁ C₁ e c) *
          ((1 : S₁) ⊗ₜ[R] (s ⊗ₜ[R] ι s')) := by
      rw [φ₀_tmul, show (g₀ F S₁ C₁ e c * ((1 : S₁) ⊗ₜ[R] ι s)) ⊗ₜ[R] s' =
        (g₀ F S₁ C₁ e c ⊗ₜ[R] (1 : S₁)) * ((((1 : S₁) ⊗ₜ[R] ι s)) ⊗ₜ[R] s') by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, map_mul, assoc_left,
        Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, φ₀_tmul, g₀_ι]
      simp [Algebra.TensorProduct.tmul_mul_tmul]

    have Rr : (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom)
        ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁)
          ((Algebra.TensorProduct.map (φ₀ F S₁ C₁ e) (AlgHom.id R S₁))
            ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm
              ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁ S₁).toAlgHom)
                ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁) ((c ⊗ₜ[R] s) ⊗ₜ[R] s')))))) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁) (g₀ F S₁ C₁ e c) *
          ((1 : S₁) ⊗ₜ[R] (s ⊗ₜ[R] ι s')) := by
      rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_apply,
        Algebra.TensorProduct.comm_tmul, AlgHom.id_apply, Algebra.TensorProduct.assoc_symm_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, φ₀_tmul,
        show (g₀ F S₁ C₁ e c * ((1 : S₁) ⊗ₜ[R] ι s')) ⊗ₜ[R] s =
          (g₀ F S₁ C₁ e c ⊗ₜ[R] (1 : S₁)) * ((((1 : S₁) ⊗ₜ[R] ι s')) ⊗ₜ[R] s) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, map_mul, assoc_right,
        Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul]
      simp [Algebra.TensorProduct.comm_tmul]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at L Rr ⊢
    rw [L, Rr, coact F S₁ C₁ e he c]

end DatumFromFunctor

theorem solution
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1) :
    ∃ φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁,
      φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S₁ C₁) (AlgHom.id R S₁)) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (IsScalarTower.toAlgHom R S₁ C₁) ∧
      (Algebra.TensorProduct.map (AlgHom.id R S₁) φ.toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁))) =
        (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁)).comp
              ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm.toAlgHom.comp
                ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁ S₁).toAlgHom).comp
                  (Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).toAlgHom)))) ∧
      ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom := by
  refine ⟨DatumFromFunctor.φ F S₁ C₁ e he, ?_, ?_, ?_⟩
  · exact DatumFromFunctor.φ₀_linear F S₁ C₁ e
  · exact DatumFromFunctor.cocycle F S₁ C₁ e he
  · intro D _ _ d x
    exact DatumFromFunctor.intertwine F S₁ C₁ e he _ _ x

end S_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
end P2MW
export P2MW.S_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ (solution)
