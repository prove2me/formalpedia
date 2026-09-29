-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.eta_eq_of_isoVia_of_corr_of_isRigTransport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ecf5a1bf-01a1-5da9-8e7c-250ed9fb6000

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_X_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_span_range_eq
import Theorems.Thm_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eta_eq_of_isoVia_of_corr_of_isRigTransport
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

namespace XD

section CurveAnchor

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def zn (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) : ↥Λ := ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩

theorem zn_coe (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) :
    ((zn hΛℤ n : ↥Λ) : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
  simp [zn]

theorem zn_eq_of_coe (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (x : ↥Λ)
    (hx : (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) : x = zn hΛℤ n :=
  Subtype.ext (by rw [hx, zn_coe])

variable {S : Type} [CommRing S]

theorem act_zn_comp (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (m n : ℕ) :
    E.act (zn hΛℤ m) ≫ E.act (zn hΛℤ n) = E.act (zn hΛℤ (n * m)) := by
  have hcoe : ((zn hΛℤ n : ↥Λ) : ℍ[ℚ, a, b]) * ((zn hΛℤ m : ↥Λ) : ℍ[ℚ, a, b]) = (((n * m : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [zn_coe, zn_coe]
    push_cast
    first | rfl | simp
  have hmem : ((zn hΛℤ n : ↥Λ) : ℍ[ℚ, a, b]) * ((zn hΛℤ m : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [hcoe, ← zn_coe hΛℤ]
    exact (zn hΛℤ (n * m)).2
  rw [← E.act_mul (zn hΛℤ n) (zn hΛℤ m) hmem]
  congr 1
  exact zn_eq_of_coe hΛℤ (n * m) _ hcoe

theorem act_zn_pow_comp (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) (r i j : ℕ) :
    E.act (zn hΛℤ (r ^ i)) ≫ E.act (zn hΛℤ (r ^ j)) = E.act (zn hΛℤ (r ^ (i + j))) := by
  rw [act_zn_comp, ← pow_add, add_comm]

theorem act_zn_one (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) :
    E.act (zn hΛℤ 1) = 𝟙 E.A := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by
    have := (zn hΛℤ 1).2
    rw [zn_coe] at this
    simpa using this
  have e : zn hΛℤ 1 = ⟨1, h1⟩ := Subtype.ext (by rw [zn_coe]; simp)
  rw [e, E.act_one h1]

theorem curve_anchor (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {r : ℕ}
    (Eb Eb' Ab Ab' : FakeEllipticCurve Λ N S)
    (φ : Eb.A ⟶ Ab.A) (φ' : Ab.A ⟶ Eb.A) (d : ℕ) (hpair : IsIsogenyPair (r ^ d) Eb Ab φ φ')
    (φ₁ : Eb'.A ⟶ Ab'.A) (φ₁' : Ab'.A ⟶ Eb'.A) (d' : ℕ) (hpair' : IsIsogenyPair (r ^ d') Eb' Ab' φ₁ φ₁')
    (ib : Eb.A ⟶ Eb'.A) (ibInv : Eb'.A ⟶ Eb.A) (h1 : ib ≫ ibInv = 𝟙 _) (h2 : ibInv ≫ ib = 𝟙 _)
    (hib : ∀ x, Eb.act x ≫ ib = ib ≫ Eb'.act x)
    (uA : Ab'.A ⟶ Ab.A) (huA : ∀ x, Ab'.act x ≫ uA = uA ≫ Ab.act x)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ φ₁ ≫ uA ≫ Ab.act (zn hΛℤ (r ^ i₁)) = φ ≫ Ab.act (zn hΛℤ (r ^ j₁))) :
    φ₁' ≫ Eb'.act (zn hΛℤ (r ^ (d + j₁ + 1))) = uA ≫ φ' ≫ ib ≫ Eb'.act (zn hΛℤ (r ^ (d' + i₁ + 1))) := by
  obtain ⟨hφo, hφ'o, -, -, hφlin, hφ'lin, hdeg⟩ := hpair
  obtain ⟨hφ₁o, hφ₁'o, -, -, hφ₁lin, hφ₁'lin, hdeg'⟩ := hpair'
  have hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← zn_coe hΛℤ]; exact (zn hΛℤ _).2
  have hd' : (((r ^ d' : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← zn_coe hΛℤ]; exact (zn hΛℤ _).2
  obtain ⟨hφφ', -⟩ := hdeg hd
  obtain ⟨-, hφ₁'φ₁⟩ := hdeg' hd'
  rw [zn_eq_of_coe hΛℤ (r ^ d) ⟨_, hd⟩ rfl] at hφφ'
  rw [zn_eq_of_coe hΛℤ (r ^ d') ⟨_, hd'⟩ rfl] at hφ₁'φ₁

  have hibInv : ∀ x, Eb'.act x ≫ ibInv = ibInv ≫ Eb.act x := fun x => by
    have := congrArg (fun k => ibInv ≫ k ≫ ibInv) (hib x)
    simp only [Category.assoc] at this
    rw [h1, Category.comp_id, ← Category.assoc, h2, Category.id_comp] at this
    exact this.symm

  have S2 : φ₁' ≫ ibInv ≫ φ ≫ Ab.act (zn hΛℤ (r ^ j₁)) =
      uA ≫ Ab.act (zn hΛℤ (r ^ d')) ≫ Ab.act (zn hΛℤ (r ^ i₁)) := by
    rw [← hcorr, ← Category.assoc ibInv ib, h2, Category.id_comp, ← Category.assoc φ₁' φ₁, hφ₁'φ₁,
      ← Category.assoc (Ab'.act _) uA, huA, Category.assoc]

  have S3 : φ₁' ≫ Eb'.act (zn hΛℤ (r ^ d)) ≫ Eb'.act (zn hΛℤ (r ^ j₁)) ≫ ibInv =
      uA ≫ φ' ≫ Eb.act (zn hΛℤ (r ^ d')) ≫ Eb.act (zn hΛℤ (r ^ i₁)) := by
    have := congrArg (fun k => k ≫ φ') S2
    simp only [Category.assoc] at this
    rw [hφ'lin, ← Category.assoc φ φ', hφφ', hφ'lin, ← Category.assoc (Ab.act _) φ', hφ'lin,
      Category.assoc] at this
    rw [← Category.assoc ibInv, ← hibInv, Category.assoc, ← hibInv] at this
    exact this

  have S4 := congrArg (fun k => k ≫ ib) S3
  simp only [Category.assoc] at S4
  rw [h2, Category.comp_id, hib, ← Category.assoc (Eb.act _) ib, hib, Category.assoc] at S4

  rw [act_zn_pow_comp, act_zn_pow_comp] at S4
  have S5 := congrArg (fun k => k ≫ Eb'.act (zn hΛℤ (r ^ 1))) S4
  simp only [Category.assoc] at S5
  rw [act_zn_pow_comp, act_zn_pow_comp] at S5
  exact S5

end CurveAnchor

end XD

namespace XD

section MoreSeries

variable {R : Type} [CommRing R]

theorem nilEval_zero (n : ℕ) (f : MvPowerSeries (Fin 2) R) :
    MvFormalGroup.nilEval n f (fun _ => (0 : R)) = MvPowerSeries.constantCoeff f := by
  classical
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.aeval_zero', Algebra.algebraMap_self_apply,
    MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_trunc',
    if_pos (show (0 : Fin 2 →₀ ℕ) ≤ Finsupp.equivFunOnFinite.symm (fun _ => n) from bot_le),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem constantCoeff_comp_eq (ψ φ : Series R) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff ((ψ.comp φ) i) = MvPowerSeries.constantCoeff (ψ i) := by
  classical
  have h1 : (⊥ : Ideal R) ^ (0 + 1) = ⊥ := by rw [zero_add, pow_one]
  rw [← nilEval_zero 0 ((ψ.comp φ) i), ← nilEval_zero 0 (ψ i),
    nilEval_seriesComp (⊥ : Ideal R) 0 h1 ψ φ hφ (fun _ => (0 : R)) (fun _ => Submodule.zero_mem _) i]
  congr 1
  funext j
  exact Ideal.mem_bot.mp (nilEval_mem (⊥ : Ideal R) 0 (φ j) (hφ j) _ (fun _ => Submodule.zero_mem _))

theorem constantCoeff_map_zero {R' : Type} [CommRing R'] (f : R →+* R') (φ : Series R)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) : MvPowerSeries.constantCoeff ((φ.map f) i) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ i, map_zero]

theorem act_pow_eq_natCast_toPowerSeries {r : ℕ} [Fact r.Prime] (X : FormalODModule r R) (k : ℕ) :
    X.act ((r : Zp2 r) ^ k) = MvFormalGroup.Hom.toPowerSeries (((r ^ k : ℕ)) : MvFormalGroup.End X.F) := by
  rw [← Nat.cast_pow, FormalODModule.act_natCast, MvFormalGroup.End.toPowerSeries_natCast]

end MoreSeries

section ActPoints

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem zn_add (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m n : ℕ) : zn hΛℤ m + zn hΛℤ n = zn hΛℤ (m + n) :=
  Subtype.ext (by
    rw [Submodule.coe_add, zn_coe, zn_coe, zn_coe]
    push_cast
    first | rfl | simp)

theorem pushPt_act_zn (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) (k : ℕ) :
    pushPt (E.act (zn hΛℤ k)) (E.act_over _) P = nsmulPt E.L t k P := by
  induction k with
  | zero =>
    have key := E.act_add (zn hΛℤ 0) (zn hΛℤ 0) t P
    rw [zn_add] at key
    letI := E.L.pointGroup t
    exact mul_eq_left.mp key.symm
  | succ k ih =>
    rw [← zn_add, E.act_add, ih]
    have h1 : pushPt (E.act (zn hΛℤ 1)) (E.act_over _) P = P :=
      Subtype.ext (by simp only [mapPt_coe, act_zn_one, Category.comp_id])
    rw [h1]
    rfl

end ActPoints

end XD

open scoped TensorProduct Quaternion NumberField in
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian in

open XD in

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (B : Type) [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hBr : IsNilpotent ((r : ℕ) : B))
    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ϱ θ j t) (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (X' : FormalODModule r B) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ')
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X')
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ϱ' θ' j' t') (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    :
    j' = j ∧ t'.n + ϱ.d + j₁ = t.n + ϱ'.d + i₁ ∧ η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t' = η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t := by
  classical
  subst htX ht'X

  obtain ⟨κB, σ, hκ1, hκ2, hrep, hρt⟩ := htr
  obtain ⟨κB', σ', hκ1', hκ2', hrep', hρt'⟩ := htr'
  have hκκ : κB' = κB := Ideal.Quotient.ringHom_ext (hκ1'.trans hκ1.symm)
  rw [hκκ] at hρt'
  clear hκ1' hκ2' hκκ
  obtain ⟨hgb, -, hgbact, -⟩ := ϱ.isPullback_Eb
  obtain ⟨hgb', -, hgb'act, -⟩ := ϱ'.isPullback_Eb
  obtain ⟨hgA', -, -, -⟩ := ϱ'.isPullback_Ab
  obtain ⟨hguA, -, huAact, -⟩ := huA
  have hiinv : i.inv ≫ E.f = E'.f := inv_over i hi

  have hDtop : pIdeal r B ≠ ⊤ := by
    intro h
    rw [Ideal.span_singleton_eq_top] at h
    obtain ⟨n, hn⟩ := hBr
    exact not_isUnit_zero (hn ▸ h.pow n)
  haveI : Nontrivial (B ⧸ pIdeal r B) := Ideal.Quotient.nontrivial_iff.mpr hDtop
  have hrπ : ((r : ℕ) : B) ∈ Ideal.span {algebraMap 𝒪 B π} := by
    have h0 : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp h0
    rw [Ideal.mem_span_singleton']
    exact ⟨algebraMap 𝒪 B w, by rw [← map_mul, hw, map_natCast]⟩
  have hκinj : Function.Injective κB := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := RingHom.congr_fun hκ1 x
    have hy := RingHom.congr_fun hκ1 y
    simp only [RingHom.comp_apply] at hx hy
    rw [hx, hy, Ideal.Quotient.eq] at hxy
    rw [Ideal.Quotient.eq]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrπ) hxy

  have hβ0 : ∀ i, MvPowerSeries.constantCoeff ((β₀.map (residueMap (ψ : Onr →+* B))) i) = 0 :=
    constantCoeff_map_zero _ β₀ hβ₀.1.constantCoeff
  have cf : ∀ (k : ℕ) i, MvPowerSeries.constantCoeff (frob r (B ⧸ pIdeal r B) k i) = 0 := fun k => constantCoeff_frob k
  have ca := constantCoeff_act (r := r) (D := (B ⧸ pIdeal r B))
  have hρA : t.ρ = ((σ.map κB).comp (β₀.map (residueMap (ψ : Onr →+* B)))).comp (frob r (B ⧸ pIdeal r B) j) := by
    rw [Series.comp_assoc _ _ _ hβ0 (cf j)]; exact hρt
  have hρ'A : t'.ρ = ((σ'.map κB).comp (β₀.map (residueMap (ψ : Onr →+* B)))).comp (frob r (B ⧸ pIdeal r B) j') := by
    rw [Series.comp_assoc _ _ _ hβ0 (cf j')]; exact hρt'
  have hσκ0 : ∀ i, MvPowerSeries.constantCoeff ((σ.map κB) i) = 0 := fun i => by
    rw [← constantCoeff_comp_eq (σ.map κB) _ (Series.constantCoeff_comp hβ0 (cf j)) i,
      ← Series.comp_assoc _ _ _ hβ0 (cf j), ← hρA]
    exact hadm.constantCoeff_ρ i
  have hσ'κ0 : ∀ i, MvPowerSeries.constantCoeff ((σ'.map κB) i) = 0 := fun i => by
    rw [← constantCoeff_comp_eq (σ'.map κB) _ (Series.constantCoeff_comp hβ0 (cf j')) i,
      ← Series.comp_assoc _ _ _ hβ0 (cf j'), ← hρ'A]
    exact hadm'.constantCoeff_ρ i
  have hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := fun i => hκinj (by
    rw [map_zero, ← MvPowerSeries.constantCoeff_map]; exact hσκ0 i)
  have hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0 := fun i => hκinj (by
    rw [map_zero, ← MvPowerSeries.constantCoeff_map]; exact hσ'κ0 i)
  have hA0 : ∀ i, MvPowerSeries.constantCoeff (((σ.map κB).comp (β₀.map (residueMap (ψ : Onr →+* B)))) i) = 0 :=
    Series.constantCoeff_comp hσκ0 hβ0
  have hA'0 : ∀ i, MvPowerSeries.constantCoeff (((σ'.map κB).comp (β₀.map (residueMap (ψ : Onr →+* B)))) i) = 0 :=
    Series.constantCoeff_comp hσ'κ0 hβ0

  obtain ⟨uH, huH, -⟩ := existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia coord hcoord.dense hBr
    E E' t.X t'.X θ θ' hX hX' i.hom hi hiso.1 hiso.2.1
  have hilin' : ∀ m : ↥Λ, E'.act m ≫ i.inv = i.inv ≫ E.act m := fun m => by
    rw [Iso.comp_inv_eq, Category.assoc, hiso.2.1 m, Iso.inv_hom_id_assoc]
  obtain ⟨vH, hvH, -⟩ := existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia coord hcoord.dense hBr
    E' E t'.X t.X θ' θ hX' hX i.inv hiinv (inv_hom_of_hom E.L E'.L i hi hiso.1) hilin'
  have hvu : vH.comp uH = FormalODModule.Hom.id t.X := by
    obtain ⟨w, -, hwuniq⟩ := existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia coord hcoord.dense hBr
      E E t.X t.X θ θ hX hX (𝟙 E.A) (Category.id_comp _) (fun t P Q => by simp only [mapPt_id]) (fun m => by simp)
    have h1 : IsFormalCompletionAlong θ θ (𝟙 E.A) (Category.id_comp _) (vH.comp uH).toSeries :=
      isFormalCompletionAlong_congr θ θ i.hom_inv_id _ _ _
        ((IsFormalCompletionAlong.id_and_comp θ θ' θ).2 i.hom hi i.inv hiinv
          (by rw [i.hom_inv_id]; exact Category.id_comp _)
          uH.toSeries vH.toSeries uH.isODHom.constantCoeff huH hvH)
    have h2 : IsFormalCompletionAlong θ θ (𝟙 E.A) (Category.id_comp _) (FormalODModule.Hom.id t.X).toSeries :=
      (IsFormalCompletionAlong.id_and_comp θ θ θ).1
    exact (hwuniq _ h1).trans (hwuniq _ h2).symm
  have huv : uH.comp vH = FormalODModule.Hom.id t'.X := by
    obtain ⟨w, -, hwuniq⟩ := existsUnique_hom_isFormalCompletionAlong_of_isFormalModuleVia coord hcoord.dense hBr
      E' E' t'.X t'.X θ' θ' hX' hX' (𝟙 E'.A) (Category.id_comp _) (fun t P Q => by simp only [mapPt_id]) (fun m => by simp)
    have h1 : IsFormalCompletionAlong θ' θ' (𝟙 E'.A) (Category.id_comp _) (uH.comp vH).toSeries :=
      isFormalCompletionAlong_congr θ' θ' i.inv_hom_id _ _ _
        ((IsFormalCompletionAlong.id_and_comp θ' θ θ').2 i.inv hiinv i.hom hi
          (by rw [i.inv_hom_id]; exact Category.id_comp _)
          vH.toSeries uH.toSeries vH.isODHom.constantCoeff hvH huH)
    have h2 : IsFormalCompletionAlong θ' θ' (𝟙 E'.A) (Category.id_comp _) (FormalODModule.Hom.id t'.X).toSeries :=
      (IsFormalCompletionAlong.id_and_comp θ' θ' θ').1
    exact (hwuniq _ h1).trans (hwuniq _ h2).symm
  have hvuS : vH.toSeries.comp uH.toSeries = Series.id B := congrArg FormalODModule.Hom.toSeries hvu
  have huvS : uH.toSeries.comp vH.toSeries = Series.id B := congrArg FormalODModule.Hom.toSeries huv
  have cu : ∀ i, MvPowerSeries.constantCoeff (uH.toSeries i) = 0 := uH.isODHom.constantCoeff
  have cv : ∀ i, MvPowerSeries.constantCoeff (vH.toSeries i) = 0 := vH.isODHom.constantCoeff
  have hvuD : ((vH.toSeries).map (Ideal.Quotient.mk (pIdeal r B))).comp ((uH.toSeries).map (Ideal.Quotient.mk (pIdeal r B))) = Series.id (B ⧸ pIdeal r B) := by
    rw [← Series.map_comp _ _ _ cu, hvuS, Series.map_id]

  obtain ⟨ibInv, h1, h2⟩ : ∃ ibInv : ϱ'.Eb.A ⟶ ϱ.Eb.A, ib ≫ ibInv = 𝟙 _ ∧ ibInv ≫ ib = 𝟙 _ := by
    refine ⟨hgb.lift (ϱ'.gb ≫ i.inv) ϱ'.Eb.f (by rw [Category.assoc, hiinv, hgb'.w]), ?_, ?_⟩
    · apply hgb.hom_ext
      · rw [Category.assoc, hgb.lift_fst, ← Category.assoc, hibg, Category.assoc, Iso.hom_inv_id, Category.comp_id,
          Category.id_comp]
      · rw [Category.assoc, hgb.lift_snd, hibf, Category.id_comp]
    · apply hgb'.hom_ext
      · rw [Category.assoc, hibg, ← Category.assoc, hgb.lift_fst, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Category.id_comp]
      · rw [Category.assoc, hibf, hgb.lift_snd, Category.id_comp]
  have hib : ∀ x, ϱ.Eb.act x ≫ ib = ib ≫ ϱ'.Eb.act x := fun x => by
    apply hgb'.hom_ext
    · rw [Category.assoc, hibg, ← Category.assoc, hgbact, Category.assoc, hiso.2.1 x, Category.assoc,
        hgb'act, ← Category.assoc ib, hibg, Category.assoc]
    · rw [Category.assoc, hibf, ϱ.Eb.act_over, Category.assoc, ϱ'.Eb.act_over, hibf]
  have ANCH := curve_anchor hΛℤ ϱ.Eb ϱ'.Eb ϱ.Ab ϱ'.Ab ϱ.φ ϱ.φ' ϱ.d ϱ.isIsogenyPair ϱ'.φ ϱ'.φ' ϱ'.d ϱ'.isIsogenyPair
    ib ibInv h1 h2 hib uA huAact i₁ j₁ hcorr

  have huAf : uA ≫ ϱ.Ab.f = ϱ'.Ab.f := by
    rw [hguA.w, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  have COORD : ((t'.X.act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1))).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp σ' =
      (uH.toSeries.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp (((t.X.act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1))).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp σ) := by
    funext i0
    apply eq_of_forall_nilEval_eq
    intro T _ _ J m hJ s hs
    letI algBT : Algebra B T := ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) T).comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).toAlgebra
    haveI : IsScalarTower B (B ⧸ Ideal.span {algebraMap 𝒪 B π}) T := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    letI algkT : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) T := ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) T).comp (Rigidification.residueLeg π ψ)).toAlgebra
    have w' : (θ₀ T s).1 ≫ A₀.f =
        Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) T)) ≫ Spec.map (CommRingCat.ofHom (Rigidification.residueLeg π ψ)) := by
      rw [(θ₀ T s).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    obtain ⟨PA', hPA'1, hPA'2⟩ : ∃ PA' : Spec (CommRingCat.of T) ⟶ ϱ'.Ab.A,
        PA' ≫ ϱ'.gA = (θ₀ T s).1 ∧ PA' ≫ ϱ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) T)) :=
      ⟨hgA'.lift _ _ w', hgA'.lift_fst _ _ _, hgA'.lift_snd _ _ _⟩
    have h3' := hrep' T rfl rfl J m hJ s hs PA' hPA'2 hPA'1
    have h3 := hrep T rfl rfl J m hJ s hs (PA' ≫ uA) (by rw [Category.assoc, huAf, hPA'2])
      (by rw [Category.assoc, huAg, hPA'1])
    have hs1 : ∀ i, MvFormalGroup.nilEval m (σ' i) s ∈ J := fun i => nilEval_mem J m _ (hσ'0 i) s hs
    have hs2 : ∀ i, MvFormalGroup.nilEval m (σ i) s ∈ J := fun i => nilEval_mem J m _ (hσ0 i) s hs
    have hs3 : ∀ i, MvFormalGroup.nilEval m (t.X.act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1)) i)
        (fun j => MvFormalGroup.nilEval m (σ j) s) ∈ J :=
      fun i => nilEval_mem J m _ (constantCoeff_act t.X _ i) _ hs2
    have eL : MvFormalGroup.nilEval m ((((t'.X.act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1))).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp σ') i0) s =
        MvFormalGroup.nilEval m (t'.X.act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1)) i0) (fun j => MvFormalGroup.nilEval m (σ' j) s) := by
      rw [nilEval_seriesComp J m hJ _ σ' hσ'0 s hs i0]
      exact nilEval_map_algebraMap m _ _
    have eR : MvFormalGroup.nilEval m (((uH.toSeries.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp
          (((t.X.act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1))).map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp σ)) i0) s =
        MvFormalGroup.nilEval m (uH.toSeries i0)
          (fun i => MvFormalGroup.nilEval m (t.X.act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1)) i)
            (fun j => MvFormalGroup.nilEval m (σ j) s)) := by
      rw [nilEval_seriesComp J m hJ _ _ (Series.constantCoeff_comp (constantCoeff_map_zero _ _ (constantCoeff_act t.X _)) hσ0)
        s hs i0]
      rw [show ((uH.toSeries.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) i0) = MvPowerSeries.map (algebraMap B (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (uH.toSeries i0) from rfl,
        nilEval_map_algebraMap]
      congr 1
      funext i
      rw [nilEval_seriesComp J m hJ _ σ hσ0 s hs i]
      exact nilEval_map_algebraMap m _ _
    rw [eL, eR]
    have key : (fun i => MvFormalGroup.nilEval m (t'.X.act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1)) i)
          (fun j => MvFormalGroup.nilEval m (σ' j) s)) =
        (fun i => MvFormalGroup.nilEval m (uH.toSeries i)
          (fun i => MvFormalGroup.nilEval m (t.X.act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1)) i)
            (fun j => MvFormalGroup.nilEval m (σ j) s))) := by
      apply (hX'.1.2 T J m hJ).2.1 _ _ (fun i => nilEval_mem J m _ (constantCoeff_act t'.X _ i) _ hs1)
        (fun i => nilEval_mem J m _ (cu i) _ hs3)
      rw [huH T J m hJ _ hs3, act_pow_eq_natCast_toPowerSeries t'.X, act_pow_eq_natCast_toPowerSeries t.X,
        theta_nilEval_natCast E'.L t'.X.F θ' hX'.1 T J m hJ _ hs1,
        theta_nilEval_natCast E.L t.X.F θ hX.1 T J m hJ _ hs2,
        ← pushPt_act_zn hΛℤ E', ← pushPt_act_zn hΛℤ E]
      apply Subtype.ext
      simp only [mapPt_coe]
      rw [← h3', ← h3]
      simp only [Category.assoc]
      rw [← hgb'act, ← Category.assoc ϱ.gb, ← hgbact, Category.assoc, ← hibg, ← Category.assoc (ϱ.Eb.act _) ib, hib,
        Category.assoc, ← Category.assoc ϱ'.φ', ANCH]
      simp only [Category.assoc]
    exact congrFun key i0

  have hY : FormalODModule.HasKernelOfDegree ((t.X.map (Ideal.Quotient.mk (pIdeal r B))).act (r : Zp2 r)) (r ^ 4) :=
    FormalODModule.hasKernelOfDegree_map (Ideal.Quotient.mk (pIdeal r B)) (t.X.act (r : Zp2 r)) (constantCoeff_act t.X _) hadm.2.1
  have hY' : FormalODModule.HasKernelOfDegree ((t'.X.map (Ideal.Quotient.mk (pIdeal r B))).act (r : Zp2 r)) (r ^ 4) :=
    FormalODModule.hasKernelOfDegree_map (Ideal.Quotient.mk (pIdeal r B)) (t'.X.act (r : Zp2 r)) (constantCoeff_act t'.X _) hadm'.2.1
  have ANCHD : ((t'.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1))).comp
        ((σ'.map κB).comp (β₀.map (residueMap (ψ : Onr →+* B)))) =
      (uH.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp (((t.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1))).comp
        ((σ.map κB).comp (β₀.map (residueMap (ψ : Onr →+* B))))) := by
    have c1 := congrArg (Series.map κB) COORD
    rw [Series.map_comp κB _ σ' hσ'0,
      Series.map_comp κB _ _ (Series.constantCoeff_comp (constantCoeff_map_zero _ _ (constantCoeff_act t.X _)) hσ0),
      Series.map_comp κB _ σ hσ0, Series.map_map, Series.map_map, Series.map_map, hκ1] at c1
    have c2 := congrArg (fun G => Series.comp G (β₀.map (residueMap (ψ : Onr →+* B)))) c1
    rw [Series.comp_assoc _ _ _ hσ'κ0 hβ0,
      Series.comp_assoc _ _ _ (Series.constantCoeff_comp (constantCoeff_map_zero _ _ (constantCoeff_act t.X _)) hσκ0) hβ0,
      Series.comp_assoc _ _ _ hσκ0 hβ0] at c2
    exact c2
  obtain ⟨hjj, hn⟩ := bookkeeping (t.X.map (Ideal.Quotient.mk (pIdeal r B))) (t'.X.map (Ideal.Quotient.mk (pIdeal r B))) hY hY' t.ρ t'.ρ hadm.constantCoeff_ρ
    hadm'.constantCoeff_ρ t.n t'.n hadm.2.2.2 hadm'.2.2.2 (uH.toSeries.map (Ideal.Quotient.mk (pIdeal r B))) (vH.toSeries.map (Ideal.Quotient.mk (pIdeal r B)))
    (constantCoeff_map_zero _ _ cu) (constantCoeff_map_zero _ _ cv) hvuD _ _ hA0 hA'0 j j' hj hj' hρA hρ'A
    (ϱ.d + j₁) (ϱ'.d + i₁) ANCHD
  have hadm'' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) := hjj ▸ hadm'
  rw [hjj] at hρ'A
  refine ⟨hjj, by omega, ?_⟩

  rw [hη.1 B _ hBr t' t hadm'' hadm]
  have KEY : ((t'.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1))).comp t'.ρ =
      (uH.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp (((t.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1))).comp t.ρ) := by
    rw [hρ'A, hρA, ← Series.comp_assoc _ _ (frob r (B ⧸ pIdeal r B) j) hA'0 (cf j), ANCHD,
      Series.comp_assoc _ _ (frob r (B ⧸ pIdeal r B) j) (Series.constantCoeff_comp (ca _ _) hA0) (cf j),
      Series.comp_assoc _ _ (frob r (B ⧸ pIdeal r B) j) hA0 (cf j)]
  have hρ0 := hadm.constantCoeff_ρ
  have hρ'0 := hadm'.constantCoeff_ρ
  have STEP : ((t.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1))).comp ((vH.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp t'.ρ) =
      ((t.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ'.d + i₁) + 1))).comp t.ρ := by
    have hvOD := vH.isODHom.map (Ideal.Quotient.mk (pIdeal r B))
    have c := congrArg (Series.comp (vH.toSeries.map (Ideal.Quotient.mk (pIdeal r B)))) KEY
    rw [← Series.comp_assoc _ _ t'.ρ (ca _ _) hρ'0, hvOD.2.1, Series.comp_assoc _ _ t'.ρ (constantCoeff_map_zero _ _ cv) hρ'0,
      ← Series.comp_assoc _ _ _ (constantCoeff_map_zero _ _ cu) (Series.constantCoeff_comp (ca _ _) hρ0), hvuD,
      Series.id_comp _ (Series.constantCoeff_comp (ca _ _) hρ0)] at c
    exact c
  refine ⟨vH.toSeries, uH.toSeries, (ϱ.d + j₁) + 1, vH.isODHom, uH.isODHom, huvS, hvuS, ?_⟩
  show ((t.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1 + t.n))).comp ((vH.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp t'.ρ) =
    ((t.X.map (Ideal.Quotient.mk (pIdeal r B))).act ((r : Zp2 r) ^ ((ϱ.d + j₁) + 1 + t'.n))).comp t.ρ
  rw [show (ϱ.d + j₁) + 1 + t'.n = t.n + ((ϱ'.d + i₁) + 1) by omega, add_comm ((ϱ.d + j₁) + 1) t.n, FormalODModule.act_pow_add _ t.n ((ϱ.d + j₁) + 1),
    FormalODModule.act_pow_add _ t.n ((ϱ'.d + i₁) + 1), Series.comp_assoc _ _ _ (ca _ _) (Series.constantCoeff_comp (constantCoeff_map_zero _ _ cv) hρ'0),
    STEP, ← Series.comp_assoc _ _ _ (ca _ _) hρ0]

end

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eta_eq_of_isoVia_of_corr_of_isRigTransport
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eta_eq_of_isoVia_of_corr_of_isRigTransport (solution)
