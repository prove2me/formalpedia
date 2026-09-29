-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b8887801-20e8-58b0-9cfd-ab9d7ef51d28

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

namespace P5FMT

variable {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B : Type} [CommRing B]

theorem nilEval_mul (F : MvFormalGroup 2 B) (φ ψ : MvFormalGroup.End F)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ) (hJ : J ^ (m + 1) = ⊥)
    (s : Fin 2 → B') (hs : ∀ i, s i ∈ J) :
    (∀ i, MvFormalGroup.nilEval m (ψ.toPowerSeries i) s ∈ J) ∧
    (fun i => MvFormalGroup.nilEval m ((φ * ψ).toPowerSeries i) s) =
      fun i => MvFormalGroup.nilEval m (φ.toPowerSeries i) (fun j => MvFormalGroup.nilEval m (ψ.toPowerSeries j) s) := by
  have h := MvFormalGroup.nilEval_subst_of_mem J m hJ s hs ψ.toPowerSeries ψ.constantCoeff_eq_zero
  refine ⟨(h (φ.toPowerSeries 0)).1, funext fun i => ?_⟩
  rw [MvFormalGroup.End.toPowerSeries_mul]
  exact (h (φ.toPowerSeries i)).2

theorem nilEval_one (E : FakeEllipticCurve Λ N B) (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ) (hJ : J ^ (m + 1) = ⊥)
    (s : Fin 2 → B') (hs : ∀ i, s i ∈ J) :
    (fun i => MvFormalGroup.nilEval m ((1 : MvFormalGroup.End X.F).toPowerSeries i) s) = s := by
  have h1' : (((1 : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [Nat.cast_one]; exact_mod_cast h1
  have key := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
    E coord hcoord X θ hE h1 1 h1' B' J m hJ s hs
  rw [Nat.cast_one] at key
  have hone : E.act ⟨((1 : ℕ) : ℚ), h1'⟩ = 𝟙 E.A := by
    rw [show (⟨((1 : ℕ) : ℚ), h1'⟩ : ↥Λ) = ⟨1, h1⟩ from Subtype.ext (by push_cast; rfl)]
    exact E.act_one h1
  have key' : θ B' (fun i => MvFormalGroup.nilEval m ((1 : MvFormalGroup.End X.F).toPowerSeries i) s) = θ B' s := by
    rw [key]
    apply Subtype.ext
    rw [mapPt_coe, hone, Category.comp_id]
  refine (hE.1.2 B' J m hJ).2.1 _ _ (fun i => ?_) hs key'
  exact (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs (1 : MvFormalGroup.End X.F).toPowerSeries
    (1 : MvFormalGroup.End X.F).constantCoeff_eq_zero 0).1 i

theorem eq_of_comp_act_natCast_eq (E : FakeEllipticCurve Λ N B) (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hu : IsUnit ((n : ℕ) : Zp2 r))
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ) (hJ : J ^ (m + 1) = ⊥)
    (s t : Fin 2 → B') (hs : ∀ i, s i ∈ J) (ht : ∀ i, t i ∈ J)
    (h : (θ B' s).1 ≫ E.act ⟨((n : ℕ) : ℚ), hn⟩ = (θ B' t).1 ≫ E.act ⟨((n : ℕ) : ℚ), hn⟩) : s = t := by
  obtain ⟨u, hu⟩ := hu
  have gi := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
    E coord hcoord X θ hE h1 n hn B' J m hJ

  have e1 : θ B' (fun i => MvFormalGroup.nilEval m (((n : MvFormalGroup.End X.F)).toPowerSeries i) s) =
      θ B' (fun i => MvFormalGroup.nilEval m (((n : MvFormalGroup.End X.F)).toPowerSeries i) t) := by
    rw [gi s hs, gi t ht]
    exact Subtype.ext (by simpa only [mapPt_coe] using h)
  have hmemn := fun (x : Fin 2 → B') (hx : ∀ i, x i ∈ J) =>
    (nilEval_mul X.F (X.actEnd (u⁻¹ : (Zp2 r)ˣ)) (n : MvFormalGroup.End X.F) J m hJ x hx)
  have e2 := (hE.1.2 B' J m hJ).2.1 _ _ (hmemn s hs).1 (hmemn t ht).1 e1

  have hinv : X.actEnd (u⁻¹ : (Zp2 r)ˣ) * (n : MvFormalGroup.End X.F) = 1 := by
    rw [← map_natCast X.actRingHom n, ← hu, ← FormalODModule.actRingHom_apply, ← map_mul, Units.inv_mul, map_one]
  have e3 := congrArg (fun x => fun i => MvFormalGroup.nilEval m ((X.actEnd (u⁻¹ : (Zp2 r)ˣ)).toPowerSeries i) x) e2
  rw [← (hmemn s hs).2, ← (hmemn t ht).2, hinv, nilEval_one E coord hcoord X θ hE h1 J m hJ s hs,
    nilEval_one E coord hcoord X θ hE h1 J m hJ t ht] at e3
  exact e3

theorem exists_comp_act_natCast_eq (E : FakeEllipticCurve Λ N B) (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hu : IsUnit ((n : ℕ) : Zp2 r))
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ) (hJ : J ^ (m + 1) = ⊥)
    (t : Fin 2 → B') (ht : ∀ i, t i ∈ J) :
    ∃ s : Fin 2 → B', (∀ i, s i ∈ J) ∧ (θ B' s).1 ≫ E.act ⟨((n : ℕ) : ℚ), hn⟩ = (θ B' t).1 := by
  obtain ⟨u, hu⟩ := hu
  have hmem := (nilEval_mul X.F (n : MvFormalGroup.End X.F) (X.actEnd (u⁻¹ : (Zp2 r)ˣ)) J m hJ t ht)
  refine ⟨fun i => MvFormalGroup.nilEval m ((X.actEnd (u⁻¹ : (Zp2 r)ˣ)).toPowerSeries i) t, hmem.1, ?_⟩
  have gi := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
    E coord hcoord X θ hE h1 n hn B' J m hJ _ hmem.1
  have hinv : (n : MvFormalGroup.End X.F) * X.actEnd (u⁻¹ : (Zp2 r)ˣ) = 1 := by
    rw [← map_natCast X.actRingHom n, ← hu, ← FormalODModule.actRingHom_apply, ← map_mul, Units.mul_inv, map_one]
  have := congrArg Subtype.val gi
  rw [mapPt_coe] at this
  rw [← this, ← hmem.2, hinv, nilEval_one E coord hcoord X θ hE h1 J m hJ t ht]

end P5FMT

namespace FMT9

variable {R : Type} [CommRing R]

theorem mapPt_schemeHomOverComp {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f) :
    mapPt φ hφ (schemeHomOverComp ψ hψ P) = schemeHomOverComp ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext
  simp only [mapPt_coe, schemeHomOverComp_coe, Category.assoc]

theorem mapPt_one {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f')
    (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  set x := mapPt φ hφ (L.one t) with hx
  have hxx : L'.mul t x x = x := by
    rw [hx, ← hhom, L.one_mul]
  calc x = L'.mul t (L'.one t) x := (L'.one_mul t x).symm
    _ = L'.mul t (L'.mul t (L'.inv t x) x) x := by rw [L'.inv_mul_cancel]
    _ = L'.mul t (L'.inv t x) (L'.mul t x x) := L'.mul_assoc t _ _ _
    _ = L'.mul t (L'.inv t x) x := by rw [hxx]
    _ = L'.one t := L'.inv_mul_cancel t x

end FMT9

open P5FMT FMT9 in
theorem solution
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B : Type} [CommRing B]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (E E' : FakeEllipticCurve Λ N B)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ)
    (X' : FormalODModule r B) (θ' : RelativeGroupLaw.FormalCoordinates E'.f 2) (hE' : E'.IsFormalModuleVia coord X' θ')
    (D : ℕ) (hD : IsUnit ((D : ℕ) : Zp2 r)) (hDΛ : ((D : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (hqq' : FakeEllipticCurve.IsIsogenyPair D E E' q q') :
    E'.IsFormalModuleVia coord X (fun (B' : Type) _ _ (s : Fin 2 → B') => mapPt q hq (θ B' s))  := by
  classical
  obtain ⟨hφ0, hψ0, hqhom, hq'hom, hqlin, hq'lin, hdeg⟩ := hqq'
  obtain ⟨hqq, hq'q⟩ := hdeg hDΛ

  have eq_q : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (P : SchemeHomOver t E.f), mapPt q hq P = mapPt q hφ0 P :=
    fun P => rfl
  obtain ⟨hnat, hloc⟩ := hE.1
  refine ⟨⟨?_, fun B' _ _ J n hJ => ?_⟩, ?_⟩
  ·
    intro B' _ _ B'' _ _ φ s hs
    show mapPt q hq (θ B'' (φ ∘ s)) = schemeHomOverComp _ _ (mapPt q hq (θ B' s))
    rw [hnat B' B'' φ s hs, mapPt_schemeHomOverComp]
  · obtain ⟨hinf, hinj, hsurj, hhom⟩ := hloc B' J n hJ
    obtain ⟨hinf', hinj', hsurj', hhom'⟩ := hE'.1.2 B' J n hJ
    refine ⟨fun s hs => ?_, fun s t hs ht hst => ?_, fun P hP => ?_, fun s t hs ht => ?_⟩
    ·
      show schemeHomOverComp _ _ (mapPt q hq (θ B' s)) = E'.L.one _
      rw [← mapPt_schemeHomOverComp, show schemeHomOverComp _ _ (θ B' s) = E.L.one _ from hinf s hs]
      exact mapPt_one E.L E'.L q hq (fun t P Q => hqhom t P Q) _
    ·
      have h2 : (θ B' s).1 ≫ E.act ⟨((D : ℕ) : ℚ), hDΛ⟩ = (θ B' t).1 ≫ E.act ⟨((D : ℕ) : ℚ), hDΛ⟩ := by
        have := congrArg (fun P => (mapPt q' hq' P).1) hst
        simpa only [mapPt_coe, Category.assoc, hqq] using this
      exact eq_of_comp_act_natCast_eq E coord hcoord X θ hE h1 D hDΛ hD J n hJ s t hs ht h2
    ·
      have hP1 : E.L.IsInfinitesimal J (mapPt q' hq' P) := by
        show schemeHomOverComp _ _ (mapPt q' hq' P) = E.L.one _
        rw [← mapPt_schemeHomOverComp, show schemeHomOverComp _ _ P = E'.L.one _ from hP]
        exact mapPt_one E'.L E.L q' hq' (fun t P Q => hq'hom t P Q) _
      obtain ⟨s₁, hs₁, hθs₁⟩ := hsurj _ hP1
      obtain ⟨s, hs, hDs⟩ := exists_comp_act_natCast_eq E coord hcoord X θ hE h1 D hDΛ hD J n hJ s₁ hs₁
      refine ⟨s, hs, ?_⟩

      obtain ⟨s', hs', hθ's'⟩ := hsurj' (mapPt q hq (θ B' s)) (by
        show schemeHomOverComp _ _ (mapPt q hq (θ B' s)) = E'.L.one _
        rw [← mapPt_schemeHomOverComp, show schemeHomOverComp _ _ (θ B' s) = E.L.one _ from hinf s hs]
        exact mapPt_one E.L E'.L q hq (fun t P Q => hqhom t P Q) _)
      obtain ⟨t', ht', hθ't'⟩ := hsurj' P hP
      have key : (θ' B' s').1 ≫ E'.act ⟨((D : ℕ) : ℚ), hDΛ⟩ = (θ' B' t').1 ≫ E'.act ⟨((D : ℕ) : ℚ), hDΛ⟩ := by
        rw [hθ's', hθ't', mapPt_coe, Category.assoc, ← hqlin, ← Category.assoc, hDs, hθs₁, mapPt_coe,
          Category.assoc, hq'q]
      have := eq_of_comp_act_natCast_eq E' coord hcoord X' θ' hE' h1 D hDΛ hD J n hJ s' t' hs' ht' key
      show mapPt q hq (θ B' s) = P
      rw [← hθ's', this, hθ't']
    ·
      show mapPt q hq (θ B' (X.F.nilMul n s t)) = E'.L.mul _ (mapPt q hq (θ B' s)) (mapPt q hq (θ B' t))
      rw [hhom s t hs ht]
      exact hqhom _ _ _
  ·
    intro B' _ _ J n hJ m s hs
    show mapPt q hq (θ B' _) = pushPt (E'.act m) (E'.act_over m) (mapPt q hq (θ B' s))
    rw [hE.2 B' J n hJ m s hs]
    apply Subtype.ext
    simp only [mapPt_coe, pushPt, Category.assoc, hqlin]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isFormalModuleVia_mapPt_of_isIsogenyPair_of_isUnit (solution)
