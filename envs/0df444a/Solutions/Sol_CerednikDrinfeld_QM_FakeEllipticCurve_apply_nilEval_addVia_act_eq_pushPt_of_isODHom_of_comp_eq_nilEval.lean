-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b683565b-1543-57b7-8785-c9c10536255a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace P2mLT

open MvPowerSeries (subst HasSubst constantCoeff subst_comp_subst_apply subst_X hasSubst_of_constantCoeff_zero
  constantCoeff_subst_eq_zero constantCoeff_X)

section SeriesAlgebra
variable {B : Type} [CommRing B]

theorem hasSubst_series {φ : Series B} (hφ : ∀ i, constantCoeff (φ i) = 0) : HasSubst φ :=
  hasSubst_of_constantCoeff_zero hφ

theorem constantCoeff_elim {φ ψ : Series B} (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    ∀ l, constantCoeff (Sum.elim φ ψ l) = 0 := by
  rintro (j | j)
  · exact hφ j
  · exact hψ j

theorem hasSubst_elim {φ ψ : Series B} (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    HasSubst (Sum.elim φ ψ) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_elim hφ hψ)

theorem constantCoeff_addVia (F : MvFormalGroup 2 B) {φ ψ : Series B}
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    ∀ i, constantCoeff (Series.addVia F φ ψ i) = 0 := fun i =>
  constantCoeff_subst_eq_zero (hasSubst_elim hφ hψ) (constantCoeff_elim hφ hψ) (F.constantCoeff_eq_zero i)

theorem addVia_comp (G : MvFormalGroup 2 B) {φ ψ γ : Series B}
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) (hγ : ∀ i, constantCoeff (γ i) = 0) :
    (Series.addVia G φ ψ).comp γ = Series.addVia G (φ.comp γ) (ψ.comp γ) := by
  funext i
  show subst γ (subst (Sum.elim φ ψ) (G.toPowerSeries i)) = subst (Sum.elim (φ.comp γ) (ψ.comp γ)) (G.toPowerSeries i)
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) (hasSubst_series hγ)]
  congr 1
  funext l
  rcases l with j | j <;> rfl

theorem comp_addVia {F G : MvFormalGroup 2 B} {γ φ ψ : Series B} (hγ : IsLawHom F G γ)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    γ.comp (Series.addVia F φ ψ) = Series.addVia G (γ.comp φ) (γ.comp ψ) := by
  funext i
  show subst (Series.addVia F φ ψ) (γ i) = subst (Sum.elim (γ.comp φ) (γ.comp ψ)) (G.toPowerSeries i)
  have h1 : (Series.addVia F φ ψ) = fun l => subst (Sum.elim φ ψ) (F.toPowerSeries l) := rfl
  rw [h1, ← subst_comp_subst_apply F.hasSubst_toPowerSeries (hasSubst_elim hφ hψ), hγ.2 i,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ?hc) (hasSubst_elim hφ hψ)]
  case hc =>
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (hγ.1 j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (hγ.1 j)
  congr 1
  funext l
  rcases l with j | j
  · show subst (Sum.elim φ ψ) (subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (γ j)) =
      subst φ (γ j)
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _) (hasSubst_elim hφ hψ)]
    congr 1
    funext l
    rw [subst_X (hasSubst_elim hφ hψ)]
    rfl
  · show subst (Sum.elim φ ψ) (subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) (γ j)) =
      subst ψ (γ j)
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _) (hasSubst_elim hφ hψ)]
    congr 1
    funext l
    rw [subst_X (hasSubst_elim hφ hψ)]
    rfl

end SeriesAlgebra

section NilEval
variable {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {C : Type} [CommRing C] [Algebra B C]

theorem nilEval_sub (n : ℕ) (a : σ → C) (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ - ψ) a = MvFormalGroup.nilEval n φ a - MvFormalGroup.nilEval n ψ a := by
  show MvPolynomial.aeval a _ = MvPolynomial.aeval a _ - MvPolynomial.aeval a _
  rw [← map_sub]
  congr 1
  ext m
  simp only [MvPowerSeries.coeff_trunc', MvPolynomial.coeff_sub, map_sub]

theorem eq_zero_of_forall_nilEval_eq_zero [IsNoetherianRing B] (G : MvPowerSeries σ B)
    (hG : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : σ → C, (∀ i, s i ∈ J) → MvFormalGroup.nilEval n G s = 0) : G = 0 := by
  have h := MvFormalGroup.mem_span_of_forall_nilEval_eq_zero (∅ : Set (MvPowerSeries σ B)) G
    (fun C _ _ J n hJ s hs _ => hG C J n hJ s hs)
  rwa [Ideal.span_empty, Ideal.mem_bot] at h

end NilEval

end P2mLT

open P2mLT in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k]

    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)

    (Y : FormalODModule r k) (γ : Series k) (hγ : FormalODModule.IsODHom XA Y γ)
    {d : ℕ} (hγker : FormalODModule.HasKernelOfDegree γ d)

    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f') (act' : ↥Λ → (A' ⟶ A'))
    (hact' : ∀ x : ↥Λ, act' x ≫ f' = f')
    (hact'_mul : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f'),
      pushPt (act' x) (hact' x) (L'.mul t P Q) = L'.mul t (pushPt (act' x) (hact' x) P) (pushPt (act' x) (hact' x) Q))
    (p : A.A ⟶ A') (hp : p ≫ f' = A.f) (hp_act : ∀ x : ↥Λ, A.act x ≫ p = p ≫ act' x)

    (θ' : RelativeGroupLaw.FormalCoordinates f' 2) (hθ' : L'.IsFormalCoordinates Y.F θ')
    (hgerm : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ p = (θ' B'' (fun i => MvFormalGroup.nilEval m (γ i) s)).1) :
    ∀ (B' : Type) [CommRing B'] [Algebra k B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ (x : ↥Λ) (s : Fin 2 → B'), (∀ i, s i ∈ J) →
        θ' B' (fun i => MvFormalGroup.nilEval m
            (Series.addVia Y.F (Y.act (coord x).1) ((Y.act (coord x).2).comp Y.varpi) i) s) =
          pushPt (act' x) (hact' x) (θ' B' s) := by
  classical
  intro B' _ _ J m hJ x s hs
  obtain ⟨hθA, hΛA⟩ := hA
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := hγ.1.1

  set ρY : Series k := Series.addVia Y.F (Y.act (coord x).1) ((Y.act (coord x).2).comp Y.varpi) with hρY
  set ρX : Series k := Series.addVia XA.F (XA.act (coord x).1) ((XA.act (coord x).2).comp XA.varpi) with hρX
  have hactY0 : ∀ (a : Zp2 r) i, MvPowerSeries.constantCoeff (Y.act a i) = 0 := fun a => (Y.isLawHom_act a).1
  have hactX0 : ∀ (a : Zp2 r) i, MvPowerSeries.constantCoeff (XA.act a i) = 0 := fun a => (XA.isLawHom_act a).1
  have hvY0 : ∀ i, MvPowerSeries.constantCoeff ((Y.act (coord x).2).comp Y.varpi i) = 0 :=
    Series.constantCoeff_comp (hactY0 _) Y.isLawHom_varpi.1
  have hvX0 : ∀ i, MvPowerSeries.constantCoeff ((XA.act (coord x).2).comp XA.varpi i) = 0 :=
    Series.constantCoeff_comp (hactX0 _) XA.isLawHom_varpi.1
  have hρY0 : ∀ i, MvPowerSeries.constantCoeff (ρY i) = 0 := constantCoeff_addVia Y.F (hactY0 _) hvY0
  have hρX0 : ∀ i, MvPowerSeries.constantCoeff (ρX i) = 0 := constantCoeff_addVia XA.F (hactX0 _) hvX0

  have hlin : ρY.comp γ = γ.comp ρX := by
    rw [hρY, hρX, addVia_comp Y.F (hactY0 _) hvY0 hγ0, comp_addVia hγ.1 (hactX0 _) hvX0, ← hγ.2.1 (coord x).1,
      Series.comp_assoc _ _ _ Y.isLawHom_varpi.1 hγ0, ← hγ.2.2,
      ← Series.comp_assoc _ _ _ hγ0 XA.isLawHom_varpi.1, ← hγ.2.1 (coord x).2,
      Series.comp_assoc _ _ _ (hactX0 _) XA.isLawHom_varpi.1]

  obtain ⟨ax, hax, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates
      L' L' Y.F Y.F θ' θ' hθ' hθ' (act' x) (hact' x) (fun t P Q => congrArg (fun P => P.1) (hact'_mul x t P Q))
  have hax0 : ∀ i, MvPowerSeries.constantCoeff (ax.toPowerSeries i) = 0 := ax.constantCoeff_eq_zero

  have hpt : ∀ (C : Type) [CommRing C] [Algebra k C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ t : Fin 2 → C, (∀ i, t i ∈ J) →
        (fun i => MvFormalGroup.nilEval n (ax.toPowerSeries i) (fun j => MvFormalGroup.nilEval n (γ j) t)) =
        (fun i => MvFormalGroup.nilEval n (ρY i) (fun j => MvFormalGroup.nilEval n (γ j) t)) := by
    intro C _ _ J n hJ t ht
    have hγt : ∀ j, MvFormalGroup.nilEval n (γ j) t ∈ J := (MvFormalGroup.nilEval_subst_of_mem J n hJ t ht γ hγ0 0).1
    have hρXt : ∀ j, MvFormalGroup.nilEval n (ρX j) t ∈ J := (MvFormalGroup.nilEval_subst_of_mem J n hJ t ht ρX hρX0 0).1
    have haxt : ∀ i, MvFormalGroup.nilEval n (ax.toPowerSeries i) (fun j => MvFormalGroup.nilEval n (γ j) t) ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J n hJ _ hγt _ hax0 0).1
    have hρYt : ∀ i, MvFormalGroup.nilEval n (ρY i) (fun j => MvFormalGroup.nilEval n (γ j) t) ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J n hJ _ hγt _ hρY0 0).1
    apply (hθ'.2 C J n hJ).2.1 _ _ haxt hρYt

    apply Subtype.ext

    rw [← hax C J n hJ _ hγt, ← hgerm C J n hJ t ht, Category.assoc, ← hp_act x, ← Category.assoc]
    have hA1 : (θA C t).1 ≫ A.act x = (θA C (fun i => MvFormalGroup.nilEval n (ρX i) t)).1 := by
      have := hΛA C J n hJ x t ht
      rw [← hρX] at this
      exact (congrArg (fun P => P.1) this).symm
    rw [hA1, hgerm C J n hJ _ hρXt]

    congr 1
    congr 1
    funext i
    have h1 := (MvFormalGroup.nilEval_subst_of_mem J n hJ t ht γ hγ0 (ρY i)).2
    have h2 := (MvFormalGroup.nilEval_subst_of_mem J n hJ t ht ρX hρX0 (γ i)).2
    have h3 : MvPowerSeries.subst γ (ρY i) = MvPowerSeries.subst ρX (γ i) := congrFun hlin i
    rw [← h2, ← h3, h1]

  have hser : ∀ i, ax.toPowerSeries i = ρY i := by
    intro i
    apply CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree γ hγ0 hγker
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_nilEval_eq_zero
    intro C _ _ J n hJ t ht
    rw [nilEval_sub, (MvFormalGroup.nilEval_subst_of_mem J n hJ t ht γ hγ0 _).2,
      (MvFormalGroup.nilEval_subst_of_mem J n hJ t ht γ hγ0 _).2, sub_eq_zero]
    exact congrFun (hpt C J n hJ t ht) i

  have : (fun i => MvFormalGroup.nilEval m (ρY i) s) = fun i => MvFormalGroup.nilEval m (ax.toPowerSeries i) s := by
    funext i; rw [hser]
  rw [this]
  apply Subtype.ext
  exact (hax B' J m hJ s hs).symm

end S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_addVia_act_eq_pushPt_of_isODHom_of_comp_eq_nilEval (solution)
