-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_and_add_eq_add_of_hasKernelOfDegree_of_comp_act_pow_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a705d7e6-7e58-5a4e-b44b-a5a3f4f97a0d

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_span_range_eq
import Theorems.Thm_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_and_add_eq_add_of_hasKernelOfDegree_of_comp_act_pow_eq_comp
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

open scoped Quaternion
open MvPowerSeries

noncomputable section

namespace XD

theorem isAdicComplete_of_pow_eq_bot {C : Type*} [CommRing C] (J : Ideal C) {M : ℕ} (hM : J ^ M = ⊥) :
    IsAdicComplete J C := by
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx M
    rw [hM] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f M, fun m => by
    by_cases hm : m ≤ M
    · exact hf hm
    · push Not at hm
      have h1 : f M ≡ f m [SMOD (J ^ M • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = M + (m - M) by omega, pow_add, hM, Ideal.bot_mul]; simp
      have h3 : (J ^ M • ⊤ : Submodule C C) = ⊥ := by rw [hM]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem nilEval_mem {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ)
    (φ : MvPowerSeries σ B) (hφ : MvPowerSeries.constantCoeff φ = 0) (s : σ → B') (hs : ∀ i, s i ∈ J) :
    MvFormalGroup.nilEval n φ s ∈ J := by
  classical
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    have : MvPolynomial.coeff 0 (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ) = 0 := by
      rw [MvPowerSeries.coeff_trunc', if_pos (show (0 : σ →₀ ℕ) ≤ Finsupp.equivFunOnFinite.symm (fun _ => n) from bot_le),
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
    rw [this, map_zero, zero_mul]
    exact Ideal.zero_mem _
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hd (Finsupp.ext hcon)
    have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr hi
    refine Ideal.mul_mem_left _ _ ?_
    rw [← Finset.mul_prod_erase _ _ hmem]
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_mem_of_mem J (hs i) _ (Nat.pos_of_ne_zero hi)

theorem exists_pow_succ_eq_bot {C : Type*} [CommRing C] {J : Ideal C} (hJ : IsNilpotent J) :
    ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨k, hk⟩ := hJ
  refine ⟨k, ?_⟩
  rw [pow_succ, hk]
  simp

theorem pow_succ_eq_bot_of_le {C : Type*} [CommRing C] {J : Ideal C} {n M : ℕ} (hn : J ^ (n + 1) = ⊥) (h : n ≤ M) :
    J ^ (M + 1) = ⊥ :=
  eq_bot_iff.mpr ((Ideal.pow_le_pow_right (show n + 1 ≤ M + 1 by omega)).trans hn.le)

section NilEval

theorem nilEval_natural {R : Type} [CommRing R] {C C' : Type} [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
    (φ : C →ₐ[R] C') (n : ℕ) (f : MvPowerSeries (Fin 2) R) (x : Fin 2 → C) :
    φ (MvFormalGroup.nilEval n f x) = MvFormalGroup.nilEval n f (φ ∘ x) := by
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem nilEval_level {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C] (J : Ideal C) {n m : ℕ}
    (hn : J ^ (n + 1) = ⊥) (hm : J ^ (m + 1) = ⊥) (f : MvPowerSeries (Fin 2) R) (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) :
    MvFormalGroup.nilEval n f x = MvFormalGroup.nilEval m f x := by
  rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn f x hx,
    MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J m hm f x hx]

theorem nilEval_map_algebraMap {B R C : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C]
    [Algebra R C] [IsScalarTower B R C] (n : ℕ) (f : MvPowerSeries (Fin 2) B) (x : Fin 2 → C) :
    MvFormalGroup.nilEval n (MvPowerSeries.map (algebraMap B R) f) x = MvFormalGroup.nilEval n f x := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_map_algebraMap]

theorem nilEval_subst {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C] (J : Ideal C) (n : ℕ)
    (hJ : J ^ (n + 1) = ⊥) (g : Fin 2 → MvPowerSeries (Fin 2) R) (hg : ∀ j, MvPowerSeries.constantCoeff (g j) = 0)
    (f : MvPowerSeries (Fin 2) R) (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) :
    MvFormalGroup.nilEval n (subst g f) x = MvFormalGroup.nilEval n f (fun j => MvFormalGroup.nilEval n (g j) x) := by
  haveI : IsAdicComplete J C := isAdicComplete_of_pow_eq_bot J hJ
  have hxr : ∀ i, x i ∈ J.radical := fun i => Ideal.le_radical (hx i)
  have hmem : ∀ j, MvFormalGroup.nilEval n (g j) x ∈ J := fun j => nilEval_mem J n (g j) (hg j) x hx
  rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ x hx,
    MvFormalGroup.adicEval_subst J hxr (hasSubst_of_constantCoeff_zero hg) f,
    MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ f _ hmem]
  congr 1
  funext j
  exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ (g j) x hx).symm

theorem nilEval_seriesComp {R : Type} [CommRing R] {C : Type} [CommRing C] [Algebra R C] (J : Ideal C) (n : ℕ)
    (hJ : J ^ (n + 1) = ⊥) (ψ φ : Series R) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (x : Fin 2 → C) (hx : ∀ i, x i ∈ J) (i : Fin 2) :
    MvFormalGroup.nilEval n ((ψ.comp φ) i) x =
      MvFormalGroup.nilEval n (ψ i) (fun j => MvFormalGroup.nilEval n (φ j) x) :=
  nilEval_subst J n hJ φ hφ (ψ i) x hx

end NilEval

theorem eq_of_forall_nilEval_eq {R : Type} [CommRing R] (G H : MvPowerSeries (Fin 2) R)
    (h : ∀ (C : Type) [CommRing C] [Algebra R C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ x : Fin 2 → C, (∀ i, x i ∈ J) → MvFormalGroup.nilEval n G x = MvFormalGroup.nilEval n H x) :
    G = H := by
  classical
  have P := MvPowerSeries.existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent (R := R) (σ := Fin 2)
    (fun C _ _ J x => MvFormalGroup.adicEval J x G) (by
      intro C C' _ _ _ _ J J' hJ hJ' φ hφ x hx
      obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
      obtain ⟨n', hn'⟩ := exists_pow_succ_eq_bot hJ'
      have hM : J ^ (n + n' + 1) = ⊥ := pow_succ_eq_bot_of_le hn (Nat.le_add_right n n')
      have hM' : J' ^ (n + n' + 1) = ⊥ := pow_succ_eq_bot_of_le hn' (Nat.le_add_left n' n)
      have hφx : ∀ i, (φ ∘ x) i ∈ J' := fun i => hφ _ (hx i)
      show MvFormalGroup.adicEval J' (φ ∘ x) G = φ (MvFormalGroup.adicEval J x G)
      rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J (n + n') hM G x hx,
        ← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J' (n + n') hM' G (φ ∘ x) hφx]
      exact (nilEval_natural φ (n + n') G x).symm)
  refine P.unique ?_ ?_
  · intro C _ _ J _ x _
    rfl
  · intro C _ _ J hJ x hx
    obtain ⟨n, hn⟩ := exists_pow_succ_eq_bot hJ
    show MvFormalGroup.adicEval J x G = MvFormalGroup.adicEval J x H
    rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn G x hx,
      ← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn H x hx]
    exact h C J n hn x hx

section Coordinates

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

theorem theta_zero (L : RelativeGroupLaw B f) {g : ℕ} (F : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (B' : Type) [CommRing B'] [Algebra B B'] :
    θ B' (fun _ => (0 : B')) = L.one (Scheme.specOver (𝒪 := B) B') := by
  classical
  have h4 := hθ.2 B' (⊥ : Ideal B') 0 (by rw [zero_add, pow_one])
  have hz : ∀ i : Fin g, (fun _ : Fin g => (0 : B')) i ∈ (⊥ : Ideal B') := fun _ => Submodule.zero_mem _
  have key := h4.2.2.2 (fun _ => 0) (fun _ => 0) hz hz
  have hnil : F.nilMul 0 (fun _ : Fin g => (0 : B')) (fun _ => 0) = fun _ => 0 := by
    funext i
    have hmem := nilEval_mem (⊥ : Ideal B') 0 (F.toPowerSeries i) (F.constantCoeff_eq_zero i)
      (Sum.elim (fun _ : Fin g => (0 : B')) fun _ => 0) (by rintro (j | j) <;> exact Submodule.zero_mem _)
    rw [Ideal.mem_bot] at hmem
    exact hmem
  rw [hnil] at key
  letI := L.pointGroup (Scheme.specOver (𝒪 := B) B')
  exact mul_eq_left.mp key.symm

theorem theta_nilEval_natCast (L : RelativeGroupLaw B f) {g : ℕ} (F : MvFormalGroup g B) [F.IsComm]
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (s : Fin g → B') (hs : ∀ i, s i ∈ J) (k : ℕ) :
    θ B' (fun i => MvFormalGroup.nilEval n (MvFormalGroup.Hom.toPowerSeries ((k : MvFormalGroup.End F)) i) s) =
      nsmulPt L (Scheme.specOver (𝒪 := B) B') k (θ B' s) := by
  classical
  induction k with
  | zero =>
    have h0 : (fun i => MvFormalGroup.nilEval n (MvFormalGroup.Hom.toPowerSeries (((0 : ℕ) : MvFormalGroup.End F)) i) s) =
        fun _ => (0 : B') := by
      funext i
      rw [Nat.cast_zero, MvFormalGroup.End.toPowerSeries_zero]
      simp [MvFormalGroup.nilEval]
    rw [h0]
    exact theta_zero L F θ hθ B'
  | succ k ih =>
    haveI : IsAdicComplete J B' := isAdicComplete_of_pow_eq_bot J hJ
    have hsrad : ∀ j, s j ∈ J.radical := fun j => Ideal.le_radical (hs j)
    set t₁ : Fin g → B' := fun j => MvFormalGroup.nilEval n
      (MvFormalGroup.Hom.toPowerSeries ((k : MvFormalGroup.End F)) j) s with ht₁
    set t₂ : Fin g → B' := fun j => MvFormalGroup.nilEval n
      (MvFormalGroup.Hom.toPowerSeries ((1 : MvFormalGroup.End F)) j) s with ht₂
    have h₁c : ∀ j, MvPowerSeries.constantCoeff (MvFormalGroup.Hom.toPowerSeries ((k : MvFormalGroup.End F)) j) = 0 :=
      fun j => MvFormalGroup.Hom.constantCoeff_eq_zero _ j
    have h₂c : ∀ j, MvPowerSeries.constantCoeff (MvFormalGroup.Hom.toPowerSeries ((1 : MvFormalGroup.End F)) j) = 0 :=
      fun j => MvFormalGroup.Hom.constantCoeff_eq_zero _ j
    have ht₁mem : ∀ j, t₁ j ∈ J := fun j => nilEval_mem J n _ (h₁c j) s hs
    have ht₂mem : ∀ j, t₂ j ∈ J := fun j => nilEval_mem J n _ (h₂c j) s hs
    have htmem : ∀ c, Sum.elim t₁ t₂ c ∈ J := by
      rintro (j | j)
      · exact ht₁mem j
      · exact ht₂mem j
    have hval : (fun i => MvFormalGroup.nilEval n
        (MvFormalGroup.Hom.toPowerSeries ((((k + 1 : ℕ)) : MvFormalGroup.End F)) i) s) = F.nilMul n t₁ t₂ := by
      funext i
      rw [Nat.cast_succ, MvFormalGroup.End.toPowerSeries_add]
      show MvFormalGroup.nilEval n (subst (Sum.elim (MvFormalGroup.Hom.toPowerSeries ((k : MvFormalGroup.End F)))
          (MvFormalGroup.Hom.toPowerSeries ((1 : MvFormalGroup.End F)))) (F.toPowerSeries i)) s =
        MvFormalGroup.nilEval n (F.toPowerSeries i) (Sum.elim t₁ t₂)
      rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs,
        MvFormalGroup.adicEval_subst_elim F J hsrad h₁c h₂c i,
        MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ (Sum.elim t₁ t₂) htmem]
      congr 1
      funext c
      rcases c with j | j
      · show MvFormalGroup.adicEval J s _ = MvFormalGroup.nilEval n _ s
        rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs]
      · show MvFormalGroup.adicEval J s _ = MvFormalGroup.nilEval n _ s
        rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs]
    have ht₂eq : t₂ = s := by
      funext j
      show MvFormalGroup.nilEval n (MvFormalGroup.Hom.toPowerSeries ((1 : MvFormalGroup.End F)) j) s = s j
      rw [MvFormalGroup.End.toPowerSeries_one, MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs]
      exact MvFormalGroup.adicEval_X J s j
    rw [hval, (hθ.2 B' J n hJ).2.2.2 t₁ t₂ ht₁mem ht₂mem, ht₂eq]
    show L.mul _ (θ B' t₁) (θ B' s) = L.mul _ (nsmulPt L _ k (θ B' s)) (θ B' s)
    rw [← ih]

end Coordinates

section Points

variable {B : Type} [CommRing B] {A A' A'' : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {f'' : A'' ⟶ Spec (CommRingCat.of B)}

theorem mapPt_mapPt (h : A ⟶ A') (hh : h ≫ f' = f) (h' : A' ⟶ A'') (hh' : h' ≫ f'' = f')
    (hhh' : (h ≫ h') ≫ f'' = f) {T : Scheme.{0}} {tT : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver tT f) :
    mapPt h' hh' (mapPt h hh P) = mapPt (h ≫ h') hhh' P :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc])

theorem mapPt_id {T : Scheme.{0}} {tT : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver tT f) :
    mapPt (𝟙 A) (Category.id_comp f) P = P :=
  Subtype.ext (by simp only [mapPt_coe, Category.comp_id])

theorem isFormalCompletionAlong_congr {g g' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    {h₁ h₂ : A ⟶ A'} (heq : h₁ = h₂) (hh₁ : h₁ ≫ f' = f) (hh₂ : h₂ ≫ f' = f)
    (φ : Fin g' → MvPowerSeries (Fin g) B) (H : IsFormalCompletionAlong θ θ' h₁ hh₁ φ) :
    IsFormalCompletionAlong θ θ' h₂ hh₂ φ := by
  subst heq
  exact H

end Points

section IsoCalculus

variable {B : Type} [CommRing B] {A A' : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)}

theorem inv_over (u : A ≅ A') (hu : u.hom ≫ f' = f) : u.inv ≫ f = f' := by
  rw [Iso.inv_comp_eq]
  exact hu.symm

theorem mapPt_hom_inv (u : A ≅ A') (hu : u.hom ≫ f' = f) {T : Scheme.{0}} {tT : T ⟶ Spec (CommRingCat.of B)}
    (P : SchemeHomOver tT f) : mapPt u.inv (inv_over u hu) (mapPt u.hom hu P) = P :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id])

theorem mapPt_inv_hom (u : A ≅ A') (hu : u.hom ≫ f' = f) {T : Scheme.{0}} {tT : T ⟶ Spec (CommRingCat.of B)}
    (P : SchemeHomOver tT f') : mapPt u.hom hu (mapPt u.inv (inv_over u hu) P) = P :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id])

theorem inv_hom_of_hom (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') (u : A ≅ A') (hu : u.hom ≫ f' = f)
    (huhom : ∀ {T : Scheme.{0}} (tT : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver tT f),
      mapPt u.hom hu (L.mul tT P Q) = L'.mul tT (mapPt u.hom hu P) (mapPt u.hom hu Q))
    {T : Scheme.{0}} (tT : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver tT f') :
    mapPt u.inv (inv_over u hu) (L'.mul tT P Q) =
      L.mul tT (mapPt u.inv (inv_over u hu) P) (mapPt u.inv (inv_over u hu) Q) := by
  have key := huhom tT (mapPt u.inv (inv_over u hu) P) (mapPt u.inv (inv_over u hu) Q)
  rw [mapPt_inv_hom, mapPt_inv_hom] at key
  rw [← key, mapPt_hom_inv]

end IsoCalculus

section Degree

variable {r : ℕ} [Fact r.Prime] {D : Type} [CommRing D]

def frob (r : ℕ) (D : Type) [CommRing D] (j : ℕ) : Series D :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (r ^ j)

omit [Fact r.Prime] in
theorem frob_apply (j : ℕ) (i : Fin 2) :
    frob r D j i = (MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (r ^ j) := rfl

theorem constantCoeff_frob (j : ℕ) (i : Fin 2) : MvPowerSeries.constantCoeff (frob r D j i) = 0 := by
  rw [frob_apply, map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)]

theorem frob_add (j k : ℕ) : frob r D (j + k) = (frob r D j).comp (frob r D k) := by
  funext i
  have hS : HasSubst (frob r D k) := hasSubst_of_constantCoeff_zero (constantCoeff_frob k)
  show (MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (r ^ (j + k)) = subst (frob r D k) ((MvPowerSeries.X i) ^ (r ^ j))
  rw [← MvPowerSeries.coe_substAlgHom hS, map_pow, MvPowerSeries.coe_substAlgHom hS, subst_X hS, frob_apply,
    ← pow_mul, ← pow_add, add_comm]

theorem constantCoeff_act (Y : FormalODModule r D) (a : Zp2 r) (i : Fin 2) :
    MvPowerSeries.constantCoeff (Y.act a i) = 0 := (Y.isLawHom_act a).1 i

theorem hkd_act_pow [IsNoetherianRing D] (Y : FormalODModule r D)
    (hY : FormalODModule.HasKernelOfDegree (Y.act (r : Zp2 r)) (r ^ 4)) :
    ∀ e : ℕ, FormalODModule.HasKernelOfDegree (Y.act ((r : Zp2 r) ^ (e + 1))) (r ^ (4 * (e + 1)))
  | 0 => by simpa only [zero_add, pow_one, mul_one] using hY
  | e + 1 => by
    have ih := hkd_act_pow Y hY e
    rw [pow_succ, Y.act_mul]
    have key := FormalODModule.HasKernelOfDegree.comp (φ := Y.act (r : Zp2 r)) (ψ := Y.act ((r : Zp2 r) ^ (e + 1)))
      (constantCoeff_act Y _) (constantCoeff_act Y _) hY ih
    rw [show r ^ 4 * r ^ (4 * (e + 1)) = r ^ (4 * (e + 1 + 1)) by ring] at key
    exact key

theorem subst_mem_span [IsNoetherianRing D] (Q : Series D) (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (g : MvPowerSeries (Fin 2) D) (hg : MvPowerSeries.constantCoeff g = 0) :
    subst Q g ∈ Ideal.span (Set.range Q) := by
  classical
  apply MvFormalGroup.mem_span_of_forall_nilEval_eq_zero
  intro C _ _ J n hJ s hs hzero
  rw [nilEval_subst J n hJ Q hQ0 g s hs]
  have h0 : (fun j => MvFormalGroup.nilEval n (Q j) s) = fun _ => (0 : C) := funext fun j => hzero (Q j) ⟨j, rfl⟩
  rw [h0]
  have hmem := nilEval_mem (⊥ : Ideal C) n g hg (fun _ => (0 : C)) (fun _ => Submodule.zero_mem _)
  rwa [Ideal.mem_bot] at hmem

theorem span_comp_eq_of_leftInverse [IsNoetherianRing D] (u v Q : Series D)
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) (hvu : v.comp u = Series.id D) :
    Ideal.span (Set.range (u.comp Q)) = Ideal.span (Set.range Q) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact subst_mem_span Q hQ0 (u i) (hu0 i)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have key : v.comp (u.comp Q) = Q := by
      rw [← Series.comp_assoc v u Q hu0 hQ0, hvu, Series.id_comp Q hQ0]
    have e : (v.comp (u.comp Q)) i ∈ Ideal.span (Set.range (u.comp Q)) :=
      subst_mem_span (u.comp Q) (Series.constantCoeff_comp hu0 hQ0) (v i) (hv0 i)
    rwa [key] at e

theorem hkd_comp_of_leftInverse [IsNoetherianRing D] (u v Q : Series D)
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) (hvu : v.comp u = Series.id D)
    {h : ℕ} (hQ : FormalODModule.HasKernelOfDegree Q (r ^ h)) :
    FormalODModule.HasKernelOfDegree (u.comp Q) (r ^ h) := by
  have hI := span_comp_eq_of_leftInverse u v Q hu0 hv0 hQ0 hvu
  refine FormalODModule.hasKernelOfDegree_of_span_range_eq r (u.comp Q) (Ideal.span (Set.range Q)) h hI
    hQ.1 hQ.2.1 ?_
  intro κ _ f
  have e1 : (Ideal.span (Set.range Q)).map (MvPowerSeries.map f) = Ideal.span (Set.range (Q.map f)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [e1]
  exact hQ.2.2 κ f

theorem bookkeeping [IsNoetherianRing D] [Nontrivial D]
    (Y Y' : FormalODModule r D)
    (hY : FormalODModule.HasKernelOfDegree (Y.act (r : Zp2 r)) (r ^ 4))
    (hY' : FormalODModule.HasKernelOfDegree (Y'.act (r : Zp2 r)) (r ^ 4))
    (ρ ρ' : Series D) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0) (hρ'0 : ∀ i, MvPowerSeries.constantCoeff (ρ' i) = 0)
    (n n' : ℕ) (hρ : FormalODModule.HasKernelOfDegree ρ (r ^ (4 * n))) (hρ' : FormalODModule.HasKernelOfDegree ρ' (r ^ (4 * n')))
    (u v : Series D) (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (hvu : v.comp u = Series.id D)
    (A A' : Series D) (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) (hA'0 : ∀ i, MvPowerSeries.constantCoeff (A' i) = 0)
    (j j' : ℕ) (hj : j ≤ 1) (hj' : j' ≤ 1)
    (hρA : ρ = A.comp (frob r D j)) (hρ'A : ρ' = A'.comp (frob r D j'))
    (e1 e2 : ℕ)
    (hanchor : (Y'.act ((r : Zp2 r) ^ (e1 + 1))).comp A' = u.comp ((Y.act ((r : Zp2 r) ^ (e2 + 1))).comp A)) :
    j' = j ∧ n' + e1 = n + e2 := by
  have hr0 : r ≠ 0 := (Fact.out : r.Prime).ne_zero
  have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
  have cf : ∀ k i, MvPowerSeries.constantCoeff (frob r D k i) = 0 := fun k => constantCoeff_frob k
  have ca := constantCoeff_act (r := r) (D := D)

  have degL : FormalODModule.HasKernelOfDegree ((Y'.act ((r : Zp2 r) ^ (e1 + 1))).comp ρ') (r ^ (4 * n' + 4 * (e1 + 1))) := by
    have h := FormalODModule.HasKernelOfDegree.comp hρ'0 (ca Y' _) hρ' (hkd_act_pow Y' hY' e1)
    rw [← pow_add] at h
    exact h
  have degR0 : FormalODModule.HasKernelOfDegree ((Y.act ((r : Zp2 r) ^ (e2 + 1))).comp ρ) (r ^ (4 * n + 4 * (e2 + 1))) := by
    have h := FormalODModule.HasKernelOfDegree.comp hρ0 (ca Y _) hρ (hkd_act_pow Y hY e2)
    rw [← pow_add] at h
    exact h
  have cAρ : ∀ i, MvPowerSeries.constantCoeff (((Y.act ((r : Zp2 r) ^ (e2 + 1))).comp ρ) i) = 0 :=
    Series.constantCoeff_comp (ca Y _) hρ0
  have degR : FormalODModule.HasKernelOfDegree (u.comp ((Y.act ((r : Zp2 r) ^ (e2 + 1))).comp ρ))
      (r ^ (4 * n + 4 * (e2 + 1))) :=
    hkd_comp_of_leftInverse u v _ hu0 hv0 cAρ hvu degR0
  rcases Nat.le_total j j' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle

    have hid : (Y'.act ((r : Zp2 r) ^ (e1 + 1))).comp ρ' =
        (u.comp ((Y.act ((r : Zp2 r) ^ (e2 + 1))).comp ρ)).comp (frob r D k) := by
      rw [hρ'A, frob_add,
        ← Series.comp_assoc (Y'.act _) A' ((frob r D j).comp (frob r D k)) hA'0 (Series.constantCoeff_comp (cf j) (cf k)),
        hanchor,
        ← Series.comp_assoc (u.comp ((Y.act _).comp A)) (frob r D j) (frob r D k) (cf j) (cf k),
        Series.comp_assoc u ((Y.act _).comp A) (frob r D j) (Series.constantCoeff_comp (ca Y _) hA0) (cf j),
        Series.comp_assoc (Y.act _) A (frob r D j) hA0 (cf j), ← hρA]
    have d2 : FormalODModule.HasKernelOfDegree ((Y'.act ((r : Zp2 r) ^ (e1 + 1))).comp ρ')
        (r ^ (4 * n + 4 * (e2 + 1) + 2 * k)) := by
      rw [hid, show r ^ (4 * n + 4 * (e2 + 1) + 2 * k) = r ^ (4 * n + 4 * (e2 + 1)) * (r ^ k) ^ 2 by ring]
      exact FormalODModule.HasKernelOfDegree.comp_X_pow degR (pow_ne_zero k hr0)
    have := FormalODModule.HasKernelOfDegree.eq_of_pow_of_pow degL d2
    omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hid : ((Y'.act ((r : Zp2 r) ^ (e1 + 1))).comp ρ').comp (frob r D k) =
        u.comp ((Y.act ((r : Zp2 r) ^ (e2 + 1))).comp ρ) := by
      rw [hρA, frob_add,
        ← Series.comp_assoc (Y.act _) A ((frob r D j').comp (frob r D k)) hA0 (Series.constantCoeff_comp (cf j') (cf k)),
        ← Series.comp_assoc u ((Y.act _).comp A) ((frob r D j').comp (frob r D k))
          (Series.constantCoeff_comp (ca Y _) hA0) (Series.constantCoeff_comp (cf j') (cf k)),
        ← hanchor,
        ← Series.comp_assoc ((Y'.act _).comp A') (frob r D j') (frob r D k) (cf j') (cf k),
        Series.comp_assoc (Y'.act _) A' (frob r D j') hA'0 (cf j'), ← hρ'A]
    have d1 : FormalODModule.HasKernelOfDegree (u.comp ((Y.act ((r : Zp2 r) ^ (e2 + 1))).comp ρ))
        (r ^ (4 * n' + 4 * (e1 + 1) + 2 * k)) := by
      rw [← hid, show r ^ (4 * n' + 4 * (e1 + 1) + 2 * k) = r ^ (4 * n' + 4 * (e1 + 1)) * (r ^ k) ^ 2 by ring]
      exact FormalODModule.HasKernelOfDegree.comp_X_pow degL (pow_ne_zero k hr0)
    have := FormalODModule.HasKernelOfDegree.eq_of_pow_of_pow d1 degR
    omega

end Degree

end XD

open XD in

theorem solution
    {r : ℕ} [Fact r.Prime] {D : Type} [CommRing D] [IsNoetherianRing D] [Nontrivial D]
    (Y Y' : FormalODModule r D)
    (hY : FormalODModule.HasKernelOfDegree (Y.act (r : Zp2 r)) (r ^ 4))
    (hY' : FormalODModule.HasKernelOfDegree (Y'.act (r : Zp2 r)) (r ^ 4))
    (ρ ρ' : Series D) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0) (hρ'0 : ∀ i, MvPowerSeries.constantCoeff (ρ' i) = 0)
    (n n' : ℕ) (hρ : FormalODModule.HasKernelOfDegree ρ (r ^ (4 * n))) (hρ' : FormalODModule.HasKernelOfDegree ρ' (r ^ (4 * n')))
    (u v : Series D) (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (hvu : v.comp u = Series.id D)
    (A A' : Series D) (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) (hA'0 : ∀ i, MvPowerSeries.constantCoeff (A' i) = 0)
    (j j' : ℕ) (hj : j ≤ 1) (hj' : j' ≤ 1)
    (hρA : ρ = A.comp (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (r ^ j)))
    (hρ'A : ρ' = A'.comp (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (r ^ j')))
    (e₁ e₂ : ℕ)
    (hanchor : (Y'.act ((r : Zp2 r) ^ (e₁ + 1))).comp A' = u.comp ((Y.act ((r : Zp2 r) ^ (e₂ + 1))).comp A)) :
    j' = j ∧ n' + e₁ = n + e₂ := by
  exact XD.bookkeeping Y Y' hY hY' ρ ρ' hρ0 hρ'0 n n' hρ hρ' u v hu0 hv0 hvu A A' hA0 hA'0 j j' hj hj' hρA hρ'A e₁ e₂ hanchor

end

end S_CerednikDrinfeld_FormalODModule_eq_and_add_eq_add_of_hasKernelOfDegree_of_comp_act_pow_eq_comp
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_and_add_eq_add_of_hasKernelOfDegree_of_comp_act_pow_eq_comp (solution)
