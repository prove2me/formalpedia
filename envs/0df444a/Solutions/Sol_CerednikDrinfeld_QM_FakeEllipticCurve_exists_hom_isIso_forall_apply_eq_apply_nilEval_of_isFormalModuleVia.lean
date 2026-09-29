-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6d9cc80f-9870-5bab-9539-ab298865fb50

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion TensorProduct NumberField
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff constantCoeff_subst_eq_zero)

noncomputable section

namespace P2mWs2C2

section Nil

variable {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C]

theorem exists_pow_succ_eq_bot {J : Ideal C} (hJ : IsNilpotent J) : ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [pow_succ, hn, zero_mul]; rfl⟩

theorem isNilpotent_of_pow_succ_eq_bot {J : Ideal C} {n : ℕ} (hJ : J ^ (n + 1) = ⊥) : IsNilpotent J :=
  ⟨n + 1, hJ⟩

theorem isNilpotent_of_mem {J : Ideal C} (hJ : IsNilpotent J) {x : C} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at this
  exact (Submodule.mem_bot C).1 this

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem aeval_mem_of_coeff_zero {σ : Type} (J : Ideal C) (p : MvPolynomial σ R) (hp : p.coeff 0 = 0)
    (a : σ → C) (ha : ∀ i, a i ∈ J) : MvPolynomial.aeval a p ∈ J := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hd0 : d = 0
  · subst hd0
    rw [hp, map_zero, zero_mul]
    exact J.zero_mem
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (Finsupp.ext fun s => by simpa using h s)
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ (Finsupp.mem_support_iff.mpr hs)]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (ha s)

theorem nilEval_mem {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal C) (n : ℕ) (φ : MvPowerSeries σ R)
    (hφ : constantCoeff φ = 0) (a : σ → C) (ha : ∀ i, a i ∈ J) : MvFormalGroup.nilEval n φ a ∈ J := by
  unfold MvFormalGroup.nilEval
  refine aeval_mem_of_coeff_zero J _ ?_ a ha
  rw [MvPowerSeries.coeff_trunc', if_pos (Finsupp.le_def.2 fun _ => Nat.zero_le _),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]

theorem adicEval_mem {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (φ : MvPowerSeries σ R) (hφ : constantCoeff φ = 0) (a : σ → C) (ha : ∀ i, a i ∈ J) :
    MvFormalGroup.adicEval J a φ ∈ J := by
  rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ φ a ha]
  exact nilEval_mem J n φ hφ a ha

theorem forall_sumElim {M : Type} {p : M → Prop} {x y : Fin 2 → M} (hx : ∀ i, p (x i)) (hy : ∀ i, p (y i)) :
    ∀ c, p (Sum.elim x y c) := by
  rintro (i | i)
  exacts [hx i, hy i]

theorem adicEval_subst_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) {x : Fin 2 → C} (hx : ∀ j, x j ∈ J)
    {φ : Series R} (hφ : ∀ i, constantCoeff (φ i) = 0) (g : MvPowerSeries (Fin 2) R) :
    MvFormalGroup.adicEval J x (subst φ g) =
      MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (φ j)) g := by
  haveI := isAdicComplete_of_isNilpotent J hJ
  exact MvFormalGroup.adicEval_subst J (fun j => Ideal.le_radical (hx j)) (hasSubst_of_constantCoeff_zero hφ) g

end Nil

theorem constantCoeff_actSeries {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B] (X : FormalODModule q B)
    (α β : Zp2 q) (i : Fin 2) :
    constantCoeff (Series.addVia X.F (X.act α) ((X.act β).comp X.varpi) i) = 0 := by
  have h0 : ∀ s, constantCoeff (Sum.elim (X.act α) ((X.act β).comp X.varpi) s) = 0 := by
    rintro (j | j)
    · exact (X.isLawHom_act α).1 j
    · exact Series.constantCoeff_comp (X.isLawHom_act β).1 X.isLawHom_varpi.1 j
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (X.F.constantCoeff_eq_zero i)

section Transition

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

abbrev Fam (B : Type) [CommRing B] : Type 1 :=
  ∀ (C : Type) [CommRing C] [Algebra B C], Ideal C → (Fin 2 → C) → (Fin 2 → C)

open Classical in

def transition (θ θ' : RelativeGroupLaw.FormalCoordinates f 2) : Fam B :=
  fun C _ _ _ x =>
    if h : ∃ s : Fin 2 → C, (∀ i, s i ∈ Ideal.span (Set.range x)) ∧ θ' C s = θ C x then Classical.choose h else x

variable {L : RelativeGroupLaw B f} {F F' : MvFormalGroup 2 B} {θ θ' : RelativeGroupLaw.FormalCoordinates f 2}

theorem transition_spec (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ')
    (C : Type) [CommRing C] [Algebra B C] (J J₁ : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) :
    (∀ i, transition θ θ' C J₁ x i ∈ J) ∧ θ' C (transition θ θ' C J₁ x) = θ C x := by
  classical
  set J₀ : Ideal C := Ideal.span (Set.range x) with hJ₀
  have hle : J₀ ≤ J := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx i)
  have hJ₀n : J₀ ^ (n + 1) = ⊥ := le_bot_iff.1 (hJ ▸ Ideal.pow_right_mono hle (n + 1))
  have hx₀ : ∀ i, x i ∈ J₀ := fun i => Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨hinto, -, -, -⟩ := hθ.2 C J₀ n hJ₀n
  obtain ⟨-, -, honto', -⟩ := hθ'.2 C J₀ n hJ₀n
  have hex : ∃ s : Fin 2 → C, (∀ i, s i ∈ Ideal.span (Set.range x)) ∧ θ' C s = θ C x :=
    honto' (θ C x) (hinto x hx₀)
  have hdef : transition θ θ' C J₁ x = Classical.choose hex := by
    unfold transition
    rw [dif_pos hex]
  rw [hdef]
  obtain ⟨hs, hθs⟩ := Classical.choose_spec hex
  exact ⟨fun i => hle (hs i), hθs⟩

theorem transition_mem (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ')
    (C : Type) [CommRing C] [Algebra B C] (J J₁ : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) (i : Fin 2) : transition θ θ' C J₁ x i ∈ J :=
  (transition_spec hθ hθ' C J J₁ n hJ x hx).1 i

theorem apply_transition (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ')
    (C : Type) [CommRing C] [Algebra B C] (J J₁ : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) : θ' C (transition θ θ' C J₁ x) = θ C x :=
  (transition_spec hθ hθ' C J J₁ n hJ x hx).2

theorem eq_transition (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ')
    (C : Type) [CommRing C] [Algebra B C] (J J₁ : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) (s : Fin 2 → C) (hs : ∀ i, s i ∈ J) (hθs : θ' C s = θ C x) :
    s = transition θ θ' C J₁ x := by
  obtain ⟨-, hinj', -, -⟩ := hθ'.2 C J n hJ
  exact hinj' s _ hs (transition_mem hθ hθ' C J J₁ n hJ x hx)
    (hθs.trans (apply_transition hθ hθ' C J J₁ n hJ x hx).symm)

theorem transition_transition (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ')
    (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) :
    transition θ' θ C J (transition θ θ' C J x) = x :=
  (eq_transition hθ' hθ C J J n hJ (transition θ θ' C J x) (transition_mem hθ hθ' C J J n hJ x hx) x hx
    (apply_transition hθ hθ' C J J n hJ x hx).symm).symm

theorem transition_natural (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ')
    (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
    (J : Ideal C) (J' : Ideal C') (hJ : IsNilpotent J) (hJ' : IsNilpotent J')
    (φ : C →ₐ[B] C') (hφ : ∀ s ∈ J, φ s ∈ J') (x : Fin 2 → C) (hx : ∀ j, x j ∈ J) :
    transition θ θ' C' J' (φ ∘ x) = φ ∘ transition θ θ' C J x := by
  obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
  obtain ⟨n', hn'⟩ := exists_pow_succ_eq_bot hJ'
  have hmem := transition_mem hθ hθ' C J J n hn x hx
  symm
  refine eq_transition hθ hθ' C' J' J' n' hn' (φ ∘ x) (fun j => hφ _ (hx j)) _ (fun j => hφ _ (hmem j)) ?_
  rw [hθ'.1 C C' φ _ (fun i => isNilpotent_of_mem hJ (hmem i)), apply_transition hθ hθ' C J J n hn x hx,
    hθ.1 C C' φ x (fun i => isNilpotent_of_mem hJ (hx i))]

theorem transition_add (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ')
    (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    (x y : Fin 2 → C) (hx : ∀ j, x j ∈ J) (hy : ∀ j, y j ∈ J) :
    transition θ θ' C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) =
      fun i => MvFormalGroup.adicEval J (Sum.elim (transition θ θ' C J x) (transition θ θ' C J y))
        (F'.toPowerSeries i) := by
  obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
  have hxm := transition_mem hθ hθ' C J J n hn x hx
  have hym := transition_mem hθ hθ' C J J n hn y hy
  have e1 : (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) = F.nilMul n x y :=
    funext fun i => (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ (forall_sumElim hx hy)).symm
  have e2 : (fun i => MvFormalGroup.adicEval J (Sum.elim (transition θ θ' C J x) (transition θ θ' C J y))
      (F'.toPowerSeries i)) = F'.nilMul n (transition θ θ' C J x) (transition θ θ' C J y) :=
    funext fun i => (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ (forall_sumElim hxm hym)).symm
  rw [e1, e2]
  symm
  refine eq_transition hθ hθ' C J J n hn (F.nilMul n x y)
    (fun i => nilEval_mem J n _ (F.constantCoeff_eq_zero i) _ (forall_sumElim hx hy))
    (F'.nilMul n (transition θ θ' C J x) (transition θ θ' C J y))
    (fun i => nilEval_mem J n _ (F'.constantCoeff_eq_zero i) _ (forall_sumElim hxm hym)) ?_
  obtain ⟨-, -, -, hhom⟩ := hθ.2 C J n hn
  obtain ⟨-, -, -, hhom'⟩ := hθ'.2 C J n hn
  rw [hhom' _ _ hxm hym, hhom _ _ hx hy, apply_transition hθ hθ' C J J n hn x hx,
    apply_transition hθ hθ' C J J n hn y hy]

end Transition

section Equivariance

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B]

theorem transition_act (coord : ↥Λ → Zp2 q × Zp2 q) (E : FakeEllipticCurve Λ N B) (X Y : FormalODModule q B)
    {θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2}
    (hX : E.IsFormalModuleVia coord X θ) (hY : E.IsFormalModuleVia coord Y θ')
    (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J) (m : ↥Λ)
    (x : Fin 2 → C) (hx : ∀ j, x j ∈ J) :
    transition θ θ' C J (fun i => MvFormalGroup.adicEval J x
        (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i)) =
      fun i => MvFormalGroup.adicEval J (transition θ θ' C J x)
        (Series.addVia Y.F (Y.act (coord m).1) ((Y.act (coord m).2).comp Y.varpi) i) := by
  obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
  have hxm := transition_mem hX.1 hY.1 C J J n hn x hx
  have e1 : (fun i => MvFormalGroup.adicEval J x
      (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i)) =
      fun i => MvFormalGroup.nilEval n
        (Series.addVia X.F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) i) x :=
    funext fun i => (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hx).symm
  have e2 : (fun i => MvFormalGroup.adicEval J (transition θ θ' C J x)
      (Series.addVia Y.F (Y.act (coord m).1) ((Y.act (coord m).2).comp Y.varpi) i)) =
      fun i => MvFormalGroup.nilEval n
        (Series.addVia Y.F (Y.act (coord m).1) ((Y.act (coord m).2).comp Y.varpi) i) (transition θ θ' C J x) :=
    funext fun i => (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hxm).symm
  rw [e1, e2]
  symm
  refine eq_transition hX.1 hY.1 C J J n hn _
    (fun i => nilEval_mem J n _ (constantCoeff_actSeries X _ _ i) _ hx) _
    (fun i => nilEval_mem J n _ (constantCoeff_actSeries Y _ _ i) _ hxm) ?_
  rw [hY.2 C J n hn m _ hxm, hX.2 C J n hn m x hx, apply_transition hX.1 hY.1 C J J n hn x hx]

theorem comp_eq_id_of_leftInverse (hq : IsNilpotent ((q : ℕ) : B)) (X Y : FormalODModule q B)
    (D : Set (Zp2 q × Zp2 q))
    (hD : ∀ (k : ℕ) (α β : Zp2 q), ∃ d ∈ D,
      d.1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧ d.2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k})
    (t s : Fam B)
    (ht_mem : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, t C J x i ∈ J)
    (hst : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → s C J (t C J x) = x)
    (u : X.Hom Y) (v : Y.Hom X)
    (hu : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, t C J x i = MvFormalGroup.adicEval J x (u.toSeries i))
    (hv : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ y : Fin 2 → C, (∀ j, y j ∈ J) → ∀ i, s C J y i = MvFormalGroup.adicEval J y (v.toSeries i)) :
    v.comp u = FormalODModule.Hom.id X := by
  have hEU :=
    CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent
      hq X X D hD (fun _ _ _ _ x => x) (fun _ _ _ _ _ _ hx => hx) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => rfl)
  refine hEU.unique ?_ ?_
  · intro C _ _ J hJ x hx i
    have htx : ∀ j, t C J x j ∈ J := ht_mem C J hJ x hx
    calc x i = s C J (t C J x) i := by rw [hst C J hJ x hx]
      _ = MvFormalGroup.adicEval J (t C J x) (v.toSeries i) := hv C J hJ _ htx i
      _ = MvFormalGroup.adicEval J (fun j => MvFormalGroup.adicEval J x (u.toSeries j)) (v.toSeries i) := by
          congr 1
          funext j
          exact hu C J hJ x hx j
      _ = MvFormalGroup.adicEval J x (subst u.toSeries (v.toSeries i)) :=
          (adicEval_subst_of_isNilpotent J hJ hx u.isODHom.constantCoeff _).symm
      _ = MvFormalGroup.adicEval J x ((v.comp u).toSeries i) := rfl
  · intro C _ _ J _ x _ i
    exact (MvFormalGroup.adicEval_X J x i).symm

end Equivariance

theorem exists_hom_isIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B))
    (E : FakeEllipticCurve Λ N B) (X Y : FormalODModule q B)
    (hX : E.IsFormalModuleOf coord X) (hY : E.IsFormalModuleOf coord Y) :
    ∃ φ : FormalODModule.Hom X Y, φ.IsIso := by
  obtain ⟨θ, hXθ⟩ := hX
  obtain ⟨θ', hYθ⟩ := hY

  set D : Set (Zp2 q × Zp2 q) := Set.range coord with hD_def
  have hD : ∀ (k : ℕ) (α β : Zp2 q), ∃ d ∈ D,
      d.1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧ d.2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k} := by
    intro k α β
    obtain ⟨m, hm⟩ := hcoord.dense k α β
    exact ⟨coord m, ⟨m, rfl⟩, hm⟩

  have key : ∀ (X Y : FormalODModule q B) (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2),
      E.IsFormalModuleVia coord X θ → E.IsFormalModuleVia coord Y θ' →
      ∃ u : X.Hom Y, ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, transition θ θ' C J x i = MvFormalGroup.adicEval J x (u.toSeries i) := by
    intro X Y θ θ' hX hY
    obtain ⟨u, hu, -⟩ :=
      CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent
        hq X Y D hD (transition θ θ')
        (fun C _ _ J hJ x hx i => by
          obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
          exact transition_mem hX.1 hY.1 C J J n hn x hx i)
        (fun C C' _ _ _ _ J J' hJ hJ' φ hφ x hx => transition_natural hX.1 hY.1 C C' J J' hJ hJ' φ hφ x hx)
        (fun C _ _ J hJ x y hx hy => transition_add hX.1 hY.1 C J hJ x y hx hy)
        (by
          rintro C _ _ J hJ _ ⟨m, rfl⟩ x hx
          exact transition_act coord E X Y hX hY C J hJ m x hx)
    exact ⟨u, hu⟩
  obtain ⟨u, hu⟩ := key X Y θ θ' hXθ hYθ
  obtain ⟨v, hv⟩ := key Y X θ' θ hYθ hXθ
  have hmem : ∀ (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2) (F F' : MvFormalGroup 2 B),
      E.L.IsFormalCoordinates F θ → E.L.IsFormalCoordinates F' θ' →
      ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, transition θ θ' C J x i ∈ J := by
    intro θ θ' F F' hθ hθ' C _ _ J hJ x hx i
    obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
    exact transition_mem hθ hθ' C J J n hn x hx i
  have hinv : ∀ (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2) (F F' : MvFormalGroup 2 B),
      E.L.IsFormalCoordinates F θ → E.L.IsFormalCoordinates F' θ' →
      ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → transition θ' θ C J (transition θ θ' C J x) = x := by
    intro θ θ' F F' hθ hθ' C _ _ J hJ x hx
    obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
    exact transition_transition hθ hθ' C J n hn x hx
  have hvu : v.comp u = FormalODModule.Hom.id X :=
    comp_eq_id_of_leftInverse hq X Y D hD (transition θ θ') (transition θ' θ)
      (hmem θ θ' X.F Y.F hXθ.1 hYθ.1) (hinv θ θ' X.F Y.F hXθ.1 hYθ.1) u v hu hv
  have huv : u.comp v = FormalODModule.Hom.id Y :=
    comp_eq_id_of_leftInverse hq Y X D hD (transition θ' θ) (transition θ θ')
      (hmem θ' θ Y.F X.F hYθ.1 hXθ.1) (hinv θ' θ Y.F X.F hYθ.1 hXθ.1) v u hv hu
  exact ⟨u, v, hvu, huv⟩

end P2mWs2C2

end

noncomputable section

namespace P2mWs2C2

theorem c2_main
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (X X' : FormalODModule q B) (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hX : E.IsFormalModuleVia coord X θ) (hX' : E.IsFormalModuleVia coord X' θ') :
    ∃ u : FormalODModule.Hom X X', u.IsIso ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (u.toSeries i) s)) ∧
      ∀ u₂ : FormalODModule.Hom X X',
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (u₂.toSeries i) s)) → u₂ = u := by
  set D : Set (Zp2 q × Zp2 q) := Set.range coord with hD_def
  have hD : ∀ (k : ℕ) (α β : Zp2 q), ∃ d ∈ D,
      d.1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧ d.2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k} := by
    intro k α β
    obtain ⟨m, hm⟩ := hcoord.dense k α β
    exact ⟨coord m, ⟨m, rfl⟩, hm⟩
  have key : ∀ (X Y : FormalODModule q B) (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2),
      E.IsFormalModuleVia coord X θ → E.IsFormalModuleVia coord Y θ' →
      ∃! u : X.Hom Y, ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, transition θ θ' C J x i = MvFormalGroup.adicEval J x (u.toSeries i) := by
    intro X Y θ θ' hX hY
    exact CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent
        hq X Y D hD (transition θ θ')
        (fun C _ _ J hJ x hx i => by
          obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
          exact transition_mem hX.1 hY.1 C J J n hn x hx i)
        (fun C C' _ _ _ _ J J' hJ hJ' φ hφ x hx => transition_natural hX.1 hY.1 C C' J J' hJ hJ' φ hφ x hx)
        (fun C _ _ J hJ x y hx hy => transition_add hX.1 hY.1 C J hJ x y hx hy)
        (by
          rintro C _ _ J hJ _ ⟨m, rfl⟩ x hx
          exact transition_act coord E X Y hX hY C J hJ m x hx)
  obtain ⟨u, hu, huniq⟩ := key X X' θ θ' hX hX'
  obtain ⟨v, hv, -⟩ := key X' X θ' θ hX' hX
  have hmem : ∀ (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2) (F F' : MvFormalGroup 2 B),
      E.L.IsFormalCoordinates F θ → E.L.IsFormalCoordinates F' θ' →
      ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, transition θ θ' C J x i ∈ J := by
    intro θ θ' F F' hθ hθ' C _ _ J hJ x hx i
    obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
    exact transition_mem hθ hθ' C J J n hn x hx i
  have hinv : ∀ (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2) (F F' : MvFormalGroup 2 B),
      E.L.IsFormalCoordinates F θ → E.L.IsFormalCoordinates F' θ' →
      ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → transition θ' θ C J (transition θ θ' C J x) = x := by
    intro θ θ' F F' hθ hθ' C _ _ J hJ x hx
    obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
    exact transition_transition hθ hθ' C J n hn x hx
  have hvu : v.comp u = FormalODModule.Hom.id X :=
    comp_eq_id_of_leftInverse hq X X' D hD (transition θ θ') (transition θ' θ)
      (hmem θ θ' X.F X'.F hX.1 hX'.1) (hinv θ θ' X.F X'.F hX.1 hX'.1) u v hu hv
  have huv : u.comp v = FormalODModule.Hom.id X' :=
    comp_eq_id_of_leftInverse hq X' X D hD (transition θ' θ) (transition θ θ')
      (hmem θ' θ X'.F X.F hX'.1 hX.1) (hinv θ' θ X'.F X.F hX'.1 hX.1) v u hv hu
  refine ⟨u, ⟨v, hvu, huv⟩, ?_, ?_⟩
  · intro B'' _ _ J n hJ s hs
    have hJn : IsNilpotent J := isNilpotent_of_pow_succ_eq_bot hJ
    have heq : (fun i => MvFormalGroup.nilEval n (u.toSeries i) s) = transition θ θ' B'' J s := by
      funext i
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs, hu B'' J hJn s hs i]
    rw [heq, apply_transition hX.1 hX'.1 B'' J J n hJ s hs]
  · intro u₂ hu₂
    apply huniq
    intro C _ _ J hJ x hx i
    obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
    have hs : ∀ i, MvFormalGroup.nilEval n (u₂.toSeries i) x ∈ J :=
      fun i => nilEval_mem J n _ (u₂.isODHom.constantCoeff i) x hx
    have := eq_transition hX.1 hX'.1 C J J n hn x hx (fun i => MvFormalGroup.nilEval n (u₂.toSeries i) x) hs
      (hu₂ C J n hn x hx).symm
    rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ x hx]
    exact (congrFun this i).symm

end P2mWs2C2

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (X X' : FormalODModule q B) (θ θ' : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hX : E.IsFormalModuleVia coord X θ) (hX' : E.IsFormalModuleVia coord X' θ') :
    ∃ u : FormalODModule.Hom X X', u.IsIso ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (u.toSeries i) s)) ∧
      ∀ u₂ : FormalODModule.Hom X X',
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (u₂.toSeries i) s)) → u₂ = u :=
  P2mWs2C2.c2_main coord hcoord B hq E X X' θ θ' hX hX'

end

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_isIso_forall_apply_eq_apply_nilEval_of_isFormalModuleVia (solution)
