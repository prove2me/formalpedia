-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/231c3c4e-c0ec-545e-9f5f-f58bef3e4198

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp
import Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia
import Theorems.Thm_QuaternionAlgebra_exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong.CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong.CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve"

open scoped Quaternion MatrixGroups
open MvPowerSeries

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule QM.FakeEllipticCurve tree QM.IsFormalCompletionAlong QM.IsFormalCompletionAlong.id_and_comp QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates QM.FakeEllipticCurve.existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia"
namespace QM
p2m_export "CerednikDrinfeld.QM" "pushPt nsmulPt FakeEllipticCurve IsOrderCoord IsFormalCompletionAlong IsFormalCompletionAlong.id_and_comp IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates FakeEllipticCurve.existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia"
namespace EndDictFormalCompat
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

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

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}

theorem pushPt_comp (h h' : A ⟶ A) (hh : h ≫ f = f) (hh' : h' ≫ f = f) (hc : (h ≫ h') ≫ f = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t f) :
    pushPt (h ≫ h') hc P = pushPt h' hh' (pushPt h hh P) :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem hom_comp (L : RelativeGroupLaw B f) (h h' : A ⟶ A) (hh : h ≫ f = f) (hh' : h' ≫ f = f)
    (hc : (h ≫ h') ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      pushPt h hh (L.mul t P Q) = L.mul t (pushPt h hh P) (pushPt h hh Q))
    (hhom' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      pushPt h' hh' (L.mul t P Q) = L.mul t (pushPt h' hh' P) (pushPt h' hh' Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f) :
    pushPt (h ≫ h') hc (L.mul t P Q) = L.mul t (pushPt (h ≫ h') hc P) (pushPt (h ≫ h') hc Q) := by
  simp only [pushPt_comp h h' hh hh' hc]
  rw [hhom, hhom']

theorem isFormalCompletionAlong_congr {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    {h₁ h₂ : A ⟶ A'} (heq : h₁ = h₂) (hh₁ : h₁ ≫ f' = f) (hh₂ : h₂ ≫ f' = f)
    (φ : Fin g' → MvPowerSeries (Fin g) B) (H : IsFormalCompletionAlong θ θ' h₁ hh₁ φ) :
    IsFormalCompletionAlong θ θ' h₂ hh₂ φ := by
  subst heq
  exact H

end Points

section OrderExtends

variable {a b : ℚ}

theorem exists_algHom_of_isOrder {R₁ : Submodule ℤ ℍ[ℚ, a, b]} (hR₁ : IsOrder R₁)
    {M : Type*} [Ring M] [Algebra ℚ M]
    (ε : ↥R₁ → M) (hadd : ∀ x y : ↥R₁, ε (x + y) = ε x + ε y) (hone : ε ⟨1, hR₁.one_mem⟩ = 1)
    (hmul : ∀ (x y : ↥R₁) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ R₁),
      ε ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = ε x * ε y) :
    ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] M, ∀ x : ↥R₁, ι (x : ℍ[ℚ, a, b]) = ε x := by
  classical
  obtain ⟨Bs, hBsmem, hBsspan⟩ := QuaternionAlgebra.IsOrder.exists_basis_span_eq hR₁

  have hzero : ε 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (add_eq_left.mp h.symm)
  let εA : ↥R₁ →+ M := { toFun := ε, map_zero' := hzero, map_add' := hadd }

  let ιL : ℍ[ℚ, a, b] →ₗ[ℚ] M := Bs.constr ℚ fun i => ε ⟨Bs i, hBsmem i⟩
  have hιL_basis : ∀ i, ιL (Bs i) = ε ⟨Bs i, hBsmem i⟩ := fun i => Bs.constr_basis ℚ _ i

  have hιL : ∀ x : ↥R₁, ιL (x : ℍ[ℚ, a, b]) = ε x := by
    intro x
    have hx : (x : ℍ[ℚ, a, b]) ∈ Submodule.span ℤ (Set.range Bs) := by rw [hBsspan]; exact x.2
    suffices h : ∀ hx' : (x : ℍ[ℚ, a, b]) ∈ R₁, ιL (x : ℍ[ℚ, a, b]) = ε ⟨x, hx'⟩ from h x.2
    refine Submodule.span_induction (p := fun y _ => ∀ hy' : y ∈ R₁, ιL y = ε ⟨y, hy'⟩) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i, rfl⟩ hy'
      exact hιL_basis i
    · intro hy'
      rw [map_zero]
      exact hzero.symm
    · intro y z hy hz ihy ihz hyz'
      have hy' : y ∈ R₁ := by rw [← hBsspan]; exact hy
      have hz' : z ∈ R₁ := by rw [← hBsspan]; exact hz
      rw [map_add, ihy hy', ihz hz']
      exact (hadd ⟨y, hy'⟩ ⟨z, hz'⟩).symm
    · intro n y hy ihy hny'
      have hy' : y ∈ R₁ := by rw [← hBsspan]; exact hy
      have h1 : ιL (n • y) = n • ιL y := map_zsmul ιL n y
      have h2 : ε ⟨n • y, hny'⟩ = n • ε ⟨y, hy'⟩ := by
        have := map_zsmul εA n ⟨y, hy'⟩
        exact this
      rw [h1, h2, ihy hy']

  have hιL_one : ιL 1 = 1 := by
    have := hιL ⟨1, hR₁.one_mem⟩
    exact this.trans hone

  have hιL_mul_basis : ∀ i (v : ℍ[ℚ, a, b]), ιL (Bs i * v) = ιL (Bs i) * ιL v := by
    intro i
    have key : ιL.comp (LinearMap.mulLeft ℚ (Bs i)) = (LinearMap.mulLeft ℚ (ιL (Bs i))).comp ιL := by
      refine Bs.ext fun j => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hιL_basis i, hιL_basis j,
        show Bs i * Bs j = ((⟨Bs i * Bs j, hR₁.mul_mem (hBsmem i) (hBsmem j)⟩ : ↥R₁) : ℍ[ℚ, a, b]) from rfl,
        hιL]
      exact hmul ⟨Bs i, hBsmem i⟩ ⟨Bs j, hBsmem j⟩ _
    intro v
    have := LinearMap.congr_fun key v
    simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply] using this
  have hιL_mul : ∀ u v : ℍ[ℚ, a, b], ιL (u * v) = ιL u * ιL v := by
    intro u v
    have key : ιL.comp (LinearMap.mulRight ℚ v) = (LinearMap.mulRight ℚ (ιL v)).comp ιL := by
      refine Bs.ext fun i => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
      exact hιL_mul_basis i v
    have := LinearMap.congr_fun key u
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply] using this
  exact ⟨AlgHom.ofLinearMap ιL hιL_one hιL_mul, fun x => hιL x⟩

end OrderExtends

end CerednikDrinfeld.QM.EndDictFormalCompat

open CerednikDrinfeld.QM.EndDictFormalCompat in
theorem solution
    {q : ℕ} [Fact q.Prime]

    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) {N : ℕ}

    {B : Type} [CommRing B] (hq : IsNilpotent (q : B))

    (A₀ : FakeEllipticCurve Λ N B) (X₀ : FormalODModule q B) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hθ₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    {a₁ b₁ : ℚ} (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁)
    (c₀ : ℕ) (e : ↥R₁ → (A₀.A ⟶ A₀.A)) (he : ∀ x : ↥R₁, e x ≫ A₀.f = A₀.f)
    (hhom : ∀ (x : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t A₀.f),
      pushPt (e x) (he x) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e x) (he x) Q))
    (hlin : ∀ (x : ↥R₁) (m : ↥Λ), A₀.act m ≫ e x = e x ≫ A₀.act m)
    (hadd : ∀ (x y : ↥R₁) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e (x + y)) (he (x + y)) P = A₀.L.mul t (pushPt (e x) (he x) P) (pushPt (e y) (he y) P))
    (hmul : ∀ (x y : ↥R₁) (hxy : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₁)
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      nsmulPt A₀.L t (q ^ c₀) (pushPt (e ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩) (he _) P) =
        pushPt (e x) (he x) (pushPt (e y) (he y) P))
    (hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t A₀.f),
      pushPt (e ⟨1, hR₁.one_mem⟩) (he _) P = nsmulPt A₀.L t (q ^ c₀) P)

    (K₀ : Type) [Field K₀] [CharZero K₀] (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀)
    (𝓔 : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀) :
    ∃ g : GL (Fin 2) K₀, ∀ (x : ↥R₁) (u : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
      IsFormalCompletionAlong θ₀ θ₀ (e x) (he x) (MvFormalGroup.Hom.toPowerSeries (u : MvFormalGroup.End X₀.F)) →
        𝓔 u = ((q : K₀) ^ c₀) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
          ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)) := by
  classical
  have hcoordθ : A₀.L.IsFormalCoordinates X₀.F θ₀ := hθ₀.1

  have hE : ∀ x : ↥R₁, ∃! u : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}),
      IsFormalCompletionAlong θ₀ θ₀ (e x) (he x) (MvFormalGroup.Hom.toPowerSeries (u : MvFormalGroup.End X₀.F)) :=
    fun x => CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia
      coord hcoord hq A₀ X₀ θ₀ hθ₀ (e x) (he x) (hhom x) (hlin x)
  choose ê hê hêu using hE
  have hêc : ∀ (x : ↥R₁) (j : Fin 2),
      MvPowerSeries.constantCoeff (MvFormalGroup.Hom.toPowerSeries (ê x : MvFormalGroup.End X₀.F) j) = 0 :=
    fun x j => MvFormalGroup.Hom.constantCoeff_eq_zero _ j

  have hadd' : ∀ x y : ↥R₁, ê (x + y) = ê x + ê y := by
    intro x y
    have H := CerednikDrinfeld.QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates θ₀ θ₀ A₀.L X₀.F
      hcoordθ (e x) (e y) (e (x + y)) (he x) (he y) (he (x + y)) (fun B' _ _ P => hadd x y _ P)
      (MvFormalGroup.Hom.toPowerSeries (ê x : MvFormalGroup.End X₀.F))
      (MvFormalGroup.Hom.toPowerSeries (ê y : MvFormalGroup.End X₀.F)) (hêc x) (hêc y) (hê x) (hê y)
    exact (hêu (x + y) (ê x + ê y) H).symm

  set one₁ : ↥R₁ := ⟨1, hR₁.one_mem⟩ with hone₁
  have hone' : ê one₁ = ((q ^ c₀ : ℕ) : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) := by
    symm
    apply hêu one₁
    intro B' _ _ J n hJ s hs
    rw [SubringClass.coe_natCast, theta_nilEval_natCast A₀.L X₀.F θ₀ hcoordθ B' J n hJ s hs (q ^ c₀)]
    exact (hone _ (θ₀ B' s)).symm

  have hmul' : ∀ (x y : ↥R₁) (hxy : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₁),
      ê one₁ * ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩ = ê x * ê y := by
    intro x y hxy
    set xy : ↥R₁ := ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩ with hxydef

    have hmor : e xy ≫ e one₁ = e y ≫ e x := by
      have key := hmul x y hxy A₀.f ⟨𝟙 A₀.A, Category.id_comp _⟩
      rw [← hone] at key
      have key' := congrArg Subtype.val key
      simpa [Category.assoc] using key'
    have hc₁ : (e xy ≫ e one₁) ≫ A₀.f = A₀.f := by rw [Category.assoc, he, he]
    have hc₂ : (e y ≫ e x) ≫ A₀.f = A₀.f := by rw [Category.assoc, he, he]
    have hF := (CerednikDrinfeld.QM.IsFormalCompletionAlong.id_and_comp θ₀ θ₀ θ₀).2
    have H₁ : IsFormalCompletionAlong θ₀ θ₀ (e xy ≫ e one₁) hc₁
        (MvFormalGroup.Hom.toPowerSeries ((ê one₁ * ê xy : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) :
          MvFormalGroup.End X₀.F)) :=
      hF (e xy) (he xy) (e one₁) (he one₁) hc₁ _ _ (hêc xy) (hê xy) (hê one₁)
    have H₂ : IsFormalCompletionAlong θ₀ θ₀ (e y ≫ e x) hc₂
        (MvFormalGroup.Hom.toPowerSeries ((ê x * ê y : Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) :
          MvFormalGroup.End X₀.F)) :=
      hF (e y) (he y) (e x) (he x) hc₂ _ _ (hêc y) (hê y) (hê x)
    have hU := CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_centralizer_isFormalCompletionAlong_of_isFormalModuleVia
      coord hcoord hq A₀ X₀ θ₀ hθ₀ (e y ≫ e x) hc₂
      (fun t P Q => hom_comp A₀.L (e y) (e x) (he y) (he x) hc₂ (hhom y) (hhom x) t P Q)
      (fun m => by rw [← Category.assoc, hlin y m, Category.assoc, hlin x m, ← Category.assoc])
    exact hU.unique (isFormalCompletionAlong_congr θ₀ θ₀ hmor hc₁ hc₂ _ H₁) H₂

  set c : K₀ := (q : K₀) ^ c₀ with hcdef
  have hc : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have h𝓔one : 𝓔 (ê one₁) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) := by
    rw [hone', map_natCast, ← map_natCast (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)), Algebra.algebraMap_eq_smul_one,
      Nat.cast_pow]
  set ε : ↥R₁ → Matrix (Fin 2) (Fin 2) K₀ := fun x => c⁻¹ • 𝓔 (ê x) with hεdef
  have hε_add : ∀ x y : ↥R₁, ε (x + y) = ε x + ε y := by
    intro x y
    simp only [hεdef, hadd', map_add, smul_add]
  have hε_one : ε one₁ = 1 := by
    simp only [hεdef, h𝓔one]
    exact inv_smul_smul₀ hc _
  have hε_mul : ∀ (x y : ↥R₁) (hxy : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₁),
      ε ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), hxy⟩ = ε x * ε y := by
    intro x y hxy
    have key := congrArg 𝓔 (hmul' x y hxy)
    rw [map_mul, map_mul, h𝓔one, smul_mul_assoc, one_mul] at key

    simp only [hεdef]
    rw [smul_mul_smul_comm, ← key, smul_smul, inv_mul_cancel_right₀ hc]

  obtain ⟨ι₁, hι₁⟩ := exists_algHom_of_isOrder hR₁ ε hε_add hε_one hε_mul
  obtain ⟨g, hg⟩ := QuaternionAlgebra.exists_generalLinearGroup_forall_algHom_apply_eq_conj_algHom_apply ha₁ hb₁ K₀ ι₀ ι₁
  refine ⟨g, fun x u hu => ?_⟩
  have hux : u = ê x := hêu x u hu
  rw [hux, ← hg, hι₁]
  simp only [hεdef]
  exact (smul_inv_smul₀ hc _).symm

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generalLinearGroup_forall_apply_eq_smul_conj_of_isFormalCompletionAlong (solution)
