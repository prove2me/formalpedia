-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/700a06ab-9e93-5aa5-94ec-04d570dbc0c0

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_val_apply_pow_eq_specMap_frobenius_comp_val_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.SpecialFormal

open MvPowerSeries

noncomputable section

namespace W25

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

section Kit

variable {R : Type} [CommRing R]

theorem constantCoeff_act {r : ℕ} [Fact r.Prime] (Y : FormalODModule r R) (a : Zp2 r) (i : Fin 2) :
    MvPowerSeries.constantCoeff (Y.act a i) = 0 := (Y.isLawHom_act a).1 i

theorem constantCoeff_map_zero {R' : Type} [CommRing R'] (f : R →+* R') (φ : Series R)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) : MvPowerSeries.constantCoeff ((φ.map f) i) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ i, map_zero]

theorem act_pow_eq_natCast_toPowerSeries {r : ℕ} [Fact r.Prime] (X : FormalODModule r R) (k : ℕ) :
    X.act ((r : Zp2 r) ^ k) = MvFormalGroup.Hom.toPowerSeries (((r ^ k : ℕ)) : MvFormalGroup.End X.F) := by
  rw [← Nat.cast_pow, FormalODModule.act_natCast, MvFormalGroup.End.toPowerSeries_natCast]

theorem constantCoeff_Xpow {r : ℕ} [Fact r.Prime] (i : Fin 2) :
    MvPowerSeries.constantCoeff ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ r) i) = 0 := by
  show MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ r) = 0
  rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (Fact.out : r.Prime).ne_zero]

theorem nilEval_X_pow {C : Type} [CommRing C] [Algebra R C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (s : Fin 2 → C) (hs : ∀ i, s i ∈ J) (i : Fin 2) (k : ℕ) :
    MvFormalGroup.nilEval n ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ k) s = s i ^ k := by
  rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ s hs,
    show ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ k) = ((MvPolynomial.X i ^ k : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) by
      rw [MvPolynomial.coe_pow, MvPolynomial.coe_X],
    MvFormalGroup.adicEval_coe, map_pow, MvPolynomial.aeval_X]

end Kit

section Zn

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def zn (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) : ↥Λ := ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩

theorem zn_coe (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) :
    ((zn hΛℤ n : ↥Λ) : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
  simp [zn]

theorem zn_eq_of_coe (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (x : ↥Λ)
    (hx : (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) : x = zn hΛℤ n :=
  Subtype.ext (by rw [hx, zn_coe])

theorem zn_add (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m n : ℕ) : zn hΛℤ m + zn hΛℤ n = zn hΛℤ (m + n) :=
  Subtype.ext (by
    rw [Submodule.coe_add, zn_coe, zn_coe, zn_coe]
    push_cast
    first | rfl | simp)

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

end Zn

end W25

end

open W25 in

theorem solution
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f)
    (hFlin : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x)
    (hFfrob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
        x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)

    (L : Type) [CommRing L] [Algebra 𝒪 L] (ψ ψ' : Onr →ₐ[𝒪] L) (hψ' : ψ' = ψ.comp (Fr : Onr →ₐ[𝒪] Onr))
    (E E' : FakeEllipticCurve Λ N L) (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t E.f),
      mapPt q hq (E.L.mul t P Q) = E'.L.mul t (mapPt q hq P) (mapPt q hq Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ q = q ≫ E'.act x)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ' E')
    (qb : ρ.Eb.A ⟶ ρ'.Eb.A) (hqb : qb ≫ ρ'.gb = ρ.gb ≫ q) (hqbf : qb ≫ ρ'.Eb.f = ρ.Eb.f)
    (uA : ρ'.Ab.A ⟶ A₀r.A)
    (huA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρ'.Ab uA)
    (huAg : uA ≫ prA = ρ'.gA)
    (Fb : ρ.Ab.A ⟶ ρ'.Ab.A) (hFb : Fb ≫ uA = ρ.gA ≫ F) (hFbf : Fb ≫ ρ'.Ab.f = ρ.Ab.f)
    (i j : ℕ)
    (hcorr : qb ≫ ρ'.φ ≫ ρ'.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ Fb ≫ ρ'.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (X : FormalODModule r L) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r L) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hX' : E'.IsFormalModuleVia coord X' θ')
    (σ : Series (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B''] [Algebra L B'']
            [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
            algebraMap L B'' = (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (Ideal.Quotient.mk _) →
            algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
              (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
            ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
              ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
                PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'')) →
                PA ≫ ρ.gA = (θ₀ B'' s).1 →
                  PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (σ' : Series (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ' : (∀ (B'' : Type) [CommRing B''] [Algebra (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B''] [Algebra L B'']
            [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
            algebraMap L B'' = (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (Ideal.Quotient.mk _) →
            algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
              (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ') →
            ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
              ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ'.Ab.A,
                PA ≫ ρ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) B'')) →
                PA ≫ ρ'.gA = (θ₀ B'' s).1 →
                  PA ≫ ρ'.φ' ≫ ρ'.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1))
    (qhat : Series L) (hq0 : ∀ i, MvPowerSeries.constantCoeff (qhat i) = 0)
    (hrep : ∀ (B'' : Type) [CommRing B''] [Algebra L B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ q = (θ' B'' (fun i => MvFormalGroup.nilEval n (qhat i) s)).1) :
    ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i))).comp
        ((Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) qhat).comp σ) =
      ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ.d + j))).comp
        (σ'.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (L ⧸ Ideal.span {algebraMap 𝒪 L π})) ^ r) := by
  classical

  obtain ⟨hgAP, -, hgAact, -⟩ := ρ.isPullback_Ab
  obtain ⟨hgb'P, -, hgb'act, -⟩ := ρ'.isPullback_Eb
  obtain ⟨huAP, -, huAact, -⟩ := huA
  obtain ⟨hφo, hφ'o, -, -, hφlin, hφ'lin, hdeg⟩ := ρ.isIsogenyPair
  obtain ⟨hφ₁o, hφ₁'o, -, -, hφ₁lin, hφ₁'lin, hdeg'⟩ := ρ'.isIsogenyPair
  have hd : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← zn_coe hΛℤ]; exact (zn hΛℤ _).2
  have hd' : (((r ^ ρ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← zn_coe hΛℤ]; exact (zn hΛℤ _).2
  obtain ⟨-, hφ'φ⟩ := hdeg hd
  obtain ⟨hφ₁φ₁', -⟩ := hdeg' hd'
  rw [zn_eq_of_coe hΛℤ (r ^ ρ.d) ⟨_, hd⟩ rfl] at hφ'φ
  rw [zn_eq_of_coe hΛℤ (r ^ ρ'.d) ⟨_, hd'⟩ rfl] at hφ₁φ₁'
  have hFblin : ∀ x, ρ.Ab.act x ≫ Fb = Fb ≫ ρ'.Ab.act x := fun x => by
    apply huAP.hom_ext
    · rw [Category.assoc, hFb, ← Category.assoc, hgAact, Category.assoc, hFlin, Category.assoc, huAact,
        ← Category.assoc Fb uA, hFb, Category.assoc]
    · rw [Category.assoc, hFbf, ρ.Ab.act_over, Category.assoc, ρ'.Ab.act_over, hFbf]

  have hcorr' : qb ≫ ρ'.φ ≫ ρ'.Ab.act (zn hΛℤ (r ^ i)) = ρ.φ ≫ Fb ≫ ρ'.Ab.act (zn hΛℤ (r ^ j)) := hcorr
  have ANCH : ρ.φ' ≫ qb ≫ ρ'.Eb.act (zn hΛℤ (r ^ (ρ'.d + i))) = Fb ≫ ρ'.φ' ≫ ρ'.Eb.act (zn hΛℤ (r ^ (ρ.d + j))) := by
    have c1 := congrArg (fun k => ρ.φ' ≫ k ≫ ρ'.φ') hcorr'
    simp only [Category.assoc] at c1
    rw [hφ₁'lin, hφ₁'lin] at c1
    rw [← Category.assoc ρ'.φ ρ'.φ', hφ₁φ₁', act_zn_pow_comp] at c1
    rw [← Category.assoc ρ.φ' ρ.φ, hφ'φ, ← Category.assoc (ρ.Ab.act _) Fb, hFblin, Category.assoc,
      ← Category.assoc (ρ'.Ab.act _) ρ'.φ', hφ₁'lin, Category.assoc, act_zn_pow_comp] at c1
    exact c1

  have hrπ : ((r : ℕ) : L) ∈ Ideal.span {algebraMap 𝒪 L π} := by
    have h0 : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.mem_span_singleton_self _
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp h0
    rw [Ideal.mem_span_singleton']
    exact ⟨algebraMap 𝒪 L w, by rw [← map_mul, hw, map_natCast]⟩

  have hlegs : ∀ (T : Type) [CommRing T] [Algebra (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T] [Fact r.Prime] (hT : CharP T r),
      (frobenius T r).comp ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)) = ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ')) := by
    intro T _ _ _ hT
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hFr x)
    have e1 : (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) ((ψ' : Onr →+* L) x) = (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) ((ψ : Onr →+* L) x) ^ r := by
      rw [← map_pow, Ideal.Quotient.eq, hψ']
      show (ψ.comp (Fr : Onr →ₐ[𝒪] Onr)) x - ψ x ^ r ∈ Ideal.span {algebraMap 𝒪 L π}
      rw [AlgHom.comp_apply, ← map_pow, ← map_sub, AlgEquiv.coe_algHom, ← hy, map_mul, AlgHom.commutes]
      exact Ideal.mem_span_singleton'.mpr ⟨ψ y, rfl⟩
    simp only [RingHom.comp_apply, FakeEllipticCurve.Rigidification.residueLeg, Ideal.quotientMap_mk, frobenius_def,
      e1, map_pow]

  funext i0
  apply eq_of_forall_nilEval_eq
  intro T _ _ J m hJ s hs
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact Subsingleton.elim _ _
  letI algLT : Algebra L T := ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).toAlgebra
  haveI : IsScalarTower L (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI hchar : CharP T r := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).mpr ?_
    have : ((r : ℕ) : T) = algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T ((Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) ((r : ℕ) : L)) := by rw [map_natCast, map_natCast]
    rw [this, Ideal.Quotient.eq_zero_iff_mem.mpr hrπ, map_zero]
  have hs' : ∀ l, s l ^ r ∈ J := fun l => Ideal.pow_mem_of_mem J (hs l) r (Fact.out : r.Prime).pos
  have hsnil : ∀ l, IsNilpotent (s l) := fun l => ⟨m + 1, by
    have h := Ideal.pow_mem_pow (hs l) (m + 1)
    rw [hJ] at h
    exact (Submodule.mem_bot _).mp h⟩

  have w : (@θ₀ T _ (RingHom.toAlgebra ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ))) s).1 ≫ A₀.f =
      Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T)) ≫
        Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) := by
    rw [(@θ₀ T _ (RingHom.toAlgebra ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ))) s).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨PA, hPAg, hPAf⟩ : ∃ PA : Spec (CommRingCat.of T) ⟶ ρ.Ab.A,
      PA ≫ ρ.gA = (@θ₀ T _ (RingHom.toAlgebra ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ))) s).1 ∧ PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T)) :=
    ⟨hgAP.lift _ _ w, hgAP.lift_fst _ _ _, hgAP.lift_snd _ _ _⟩
  have h3 := @hσ T _ _ _ (RingHom.toAlgebra ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ))) rfl rfl J m hJ s hs PA hPAf hPAg
  have eF := RelativeGroupLaw.IsFormalCoordinates.val_apply_pow_eq_specMap_frobenius_comp_val_apply hA₀.1 r T ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)) s hsnil
  rw [hlegs T hchar] at eF
  have hPA'g : (PA ≫ Fb) ≫ ρ'.gA = (@θ₀ T _ (RingHom.toAlgebra ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ'))) (fun l => s l ^ r)).1 := by
    rw [eF, Category.assoc, ← huAg, ← Category.assoc Fb uA, hFb, Category.assoc, ← Category.assoc PA, hPAg]
    exact hFfrob T _
  have hPA'f : (PA ≫ Fb) ≫ ρ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T)) := by
    rw [Category.assoc, hFbf, hPAf]
  have h3' := @hσ' T _ _ _ (RingHom.toAlgebra ((algebraMap (L ⧸ Ideal.span {algebraMap 𝒪 L π}) T).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ'))) rfl rfl J m hJ (fun l => s l ^ r) hs' (PA ≫ Fb) hPA'f hPA'g

  have hσs : ∀ l, MvFormalGroup.nilEval m (σ l) s ∈ J := fun l => nilEval_mem J m _ (hσ0 l) s hs
  have hqσs : ∀ l, MvFormalGroup.nilEval m (qhat l) (fun l => MvFormalGroup.nilEval m (σ l) s) ∈ J :=
    fun l => nilEval_mem J m _ (hq0 l) _ hσs
  have hσ's : ∀ l, MvFormalGroup.nilEval m (σ' l) (fun l => s l ^ r) ∈ J := fun l => nilEval_mem J m _ (hσ'0 l) _ hs'

  have cfrob : ∀ l, MvPowerSeries.constantCoeff ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (L ⧸ Ideal.span {algebraMap 𝒪 L π})) ^ r) l) = 0 :=
    constantCoeff_Xpow
  have eL : MvFormalGroup.nilEval m ((((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i))).comp ((Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π})) qhat).comp σ)) i0) s =
      MvFormalGroup.nilEval m (X'.act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i)) i0)
        (fun l => MvFormalGroup.nilEval m (qhat l) (fun l => MvFormalGroup.nilEval m (σ l) s)) := by
    rw [nilEval_seriesComp J m hJ _ _ (Series.constantCoeff_comp (constantCoeff_map_zero _ _ hq0) hσ0) s hs i0]
    rw [show ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i))) i0 = MvPowerSeries.map (algebraMap L (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (X'.act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i)) i0) from rfl,
      nilEval_map_algebraMap]
    congr 1
    funext l
    rw [nilEval_seriesComp J m hJ _ σ hσ0 s hs l]
    exact nilEval_map_algebraMap m _ _
  have eR : MvFormalGroup.nilEval m ((((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ.d + j))).comp
        (σ'.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (L ⧸ Ideal.span {algebraMap 𝒪 L π})) ^ r)) i0) s =
      MvFormalGroup.nilEval m (X'.act (((r : ℕ) : Zp2 r) ^ (ρ.d + j)) i0)
        (fun l => MvFormalGroup.nilEval m (σ' l) (fun l => s l ^ r)) := by
    rw [nilEval_seriesComp J m hJ _ _ (Series.constantCoeff_comp hσ'0 cfrob) s hs i0]
    rw [show ((X'.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 L π}))).act (((r : ℕ) : Zp2 r) ^ (ρ.d + j))) i0 = MvPowerSeries.map (algebraMap L (L ⧸ Ideal.span {algebraMap 𝒪 L π})) (X'.act (((r : ℕ) : Zp2 r) ^ (ρ.d + j)) i0) from rfl,
      nilEval_map_algebraMap]
    congr 1
    funext l
    rw [nilEval_seriesComp J m hJ σ' _ cfrob s hs l]
    congr 1
    funext l'
    exact nilEval_X_pow J m hJ s hs l' r
  rw [eL, eR]
  have key : (fun i1 => MvFormalGroup.nilEval m (X'.act (((r : ℕ) : Zp2 r) ^ (ρ'.d + i)) i1)
        (fun l => MvFormalGroup.nilEval m (qhat l) (fun l => MvFormalGroup.nilEval m (σ l) s))) =
      (fun i1 => MvFormalGroup.nilEval m (X'.act (((r : ℕ) : Zp2 r) ^ (ρ.d + j)) i1)
        (fun l => MvFormalGroup.nilEval m (σ' l) (fun l => s l ^ r))) := by
    apply (hX'.1.2 T J m hJ).2.1 _ _ (fun i1 => nilEval_mem J m _ (constantCoeff_act X' _ i1) _ hqσs)
      (fun i1 => nilEval_mem J m _ (constantCoeff_act X' _ i1) _ hσ's)
    rw [act_pow_eq_natCast_toPowerSeries X' (ρ'.d + i), act_pow_eq_natCast_toPowerSeries X' (ρ.d + j),
      theta_nilEval_natCast E'.L X'.F θ' hX'.1 T J m hJ _ hqσs,
      theta_nilEval_natCast E'.L X'.F θ' hX'.1 T J m hJ _ hσ's,
      ← pushPt_act_zn hΛℤ E', ← pushPt_act_zn hΛℤ E']
    apply Subtype.ext
    simp only [mapPt_coe]
    rw [← hrep T J m hJ _ hσs, ← h3, ← h3']
    simp only [Category.assoc]
    rw [← Category.assoc ρ.gb q, ← hqb, Category.assoc, ← hgb'act, ← hgb'act, reassoc_of% ANCH]
  exact congrFun key i0

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_act_pow_comp_map_comp_eq_act_pow_comp_comp_frob_of_corr_relFrobenius_of_represents (solution)
