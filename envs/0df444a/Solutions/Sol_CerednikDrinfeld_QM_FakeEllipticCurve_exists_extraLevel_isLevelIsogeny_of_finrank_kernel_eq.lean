-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/dae05e50-2974-556d-856e-1f0f6f99eb62

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.GroupTheory.OrderOfElement
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace KVAux

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem one_coe (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (E.L.one t).1 = t ≫ (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  have h := E.L.one_natural (𝟙 (Spec (CommRingCat.of S))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem nsmulPt_eq_pow (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f) (n : ℕ) :
    letI := E.L.pointGroup t
    nsmulPt E.L t n P = P ^ n := by
  letI := E.L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    show E.L.mul t (nsmulPt E.L t n P) P = P ^ (n + 1)
    rw [ih, pow_succ]; rfl

theorem mapPt_one {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  have h := hhom t (E.L.one t) (E.L.one t)
  rw [E.L.one_mul] at h
  letI := E'.L.pointGroup t
  have h' : (mapPt φ hφ (E.L.one t)) * (mapPt φ hφ (E.L.one t)) = mapPt φ hφ (E.L.one t) := h.symm
  exact mul_eq_left.mp h'

theorem mapPt_inv {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt φ hφ (E.L.inv t P) = E'.L.inv t (mapPt φ hφ P) := by
  letI := E.L.pointGroup t
  letI := E'.L.pointGroup t
  let f : SchemeHomOver t E.f →* SchemeHomOver t E'.f :=
    { toFun := mapPt φ hφ, map_one' := mapPt_one φ hφ hhom t, map_mul' := hhom t }
  exact map_inv f P

end KVAux

set_option maxHeartbeats 8000000 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (E E' : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f)
    (φ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (φ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) (ψ_act : ∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x)
    (hψφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t ℓ Q)
    (φ_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P))

    (hfin : IsFinite (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f))
    (hlfp : LocallyOfFinitePresentation (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f))
    (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ E.f).finrank s = ℓ ^ 2)
    (hfibre : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), (ℓ : k') ≠ 0 →
      ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (geomPoint k' sk) E.f // FactorsThrough (pullback.fst φ (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1) P},
        ∀ x y : ZMod ℓ × ZMod ℓ, (e (x + y) : SchemeHomOver (geomPoint k' sk) E.f) = E.L.mul (geomPoint k' sk) (e x) (e y)) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔ mapPt φ hφ P = E'.L.one t) ∧
      IsLevelIsogeny ℓ (⟨E, K⟩ : WithExtraLevel Λ N ℓ k) E' := by
  classical
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.one_mem

  let e₀ : Spec (CommRingCat.of k) ⟶ E'.A := (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).1
  have he₀ : e₀ ≫ E'.f = 𝟙 _ := (E'.L.one (𝟙 (Spec (CommRingCat.of k)))).2
  let ι : pullback φ e₀ ⟶ E.A := pullback.fst φ e₀
  have hcond : ι ≫ φ = pullback.snd φ e₀ ≫ e₀ := pullback.condition

  have hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough ι P ↔ mapPt φ hφ P = E'.L.one t := by
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      have hsnd : P₀ ≫ pullback.snd φ e₀ = t := by
        have h0 : P₀ ≫ pullback.snd φ e₀ = (P₀ ≫ pullback.snd φ e₀) ≫ (e₀ ≫ E'.f) := by
          rw [he₀, Category.comp_id]
        rw [h0, Category.assoc, ← Category.assoc (pullback.snd φ e₀) e₀ E'.f, ← hcond, Category.assoc, hφ,
          ← Category.assoc, hP₀, P.2]
      apply Subtype.ext
      rw [mapPt_coe, KVAux.one_coe, ← hP₀, Category.assoc, hcond, ← Category.assoc, hsnd]
    · intro h
      have h' : P.1 ≫ φ = t ≫ e₀ := by
        have := congrArg Subtype.val h
        rw [mapPt_coe, KVAux.one_coe] at this
        exact this
      exact ⟨pullback.lift P.1 t h', pullback.lift_fst _ _ _⟩
  refine ⟨{ K := pullback φ e₀
            levK := ι
            levK_closed := ?_
            levK_sub := ?_
            levK_one := ?_
            levK_torsion := ?_
            levK_stable := ?_
            levK_disjoint := ?_
            levK_finite := ?_
            levK_flat := ?_
            levK_finitePresentation := ?_
            levK_rank := ?_
            levK_fibre := ?_ }, ?_, ?_⟩
  ·
    haveI : IsProper E'.f := E'.bundle.proper
    haveI : IsClosedImmersion (e₀ ≫ E'.f) := by rw [he₀]; infer_instance
    haveI : IsClosedImmersion e₀ := IsClosedImmersion.of_comp e₀ E'.f
    show IsClosedImmersion (pullback.fst φ e₀)
    infer_instance
  ·
    intro T t P Q hP hQ
    rw [hker] at hP hQ
    constructor
    · rw [hker, φ_hom, hP, hQ, E'.L.one_mul]
    · rw [hker, KVAux.mapPt_inv φ hφ φ_hom, hP]
      letI := E'.L.pointGroup t
      show (1 : SchemeHomOver t E'.f)⁻¹ = 1
      exact inv_one
  ·
    intro T t
    rw [hker]
    exact KVAux.mapPt_one φ hφ φ_hom t
  ·
    intro T t P hP
    rw [hker] at hP
    rw [← hψφ, hP]
    exact KVAux.mapPt_one ψ hψ ψ_hom t
  ·
    intro x T t P hP
    rw [hker] at hP ⊢
    have : mapPt φ hφ (pushPt (E.act x) (E.act_over x) P) = pushPt (E'.act x) (E'.act_over x) (mapPt φ hφ P) := by
      apply Subtype.ext
      simp only [mapPt_coe, Category.assoc, φ_act]
    rw [this, hP]
    exact KVAux.mapPt_one (E := E') (E' := E') (E'.act x) (E'.act_over x) (E'.act_hom x) t
  ·
    intro T t P hP hC
    have hℓ : nsmulPt E.L t ℓ P = E.L.one t := by
      rw [hker] at hP
      rw [← hψφ, hP]
      exact KVAux.mapPt_one ψ hψ ψ_hom t
    have hN : nsmulPt E.L t N P = E.L.one t := E.lev_torsion t P hC
    letI := E.L.pointGroup t
    have hℓ' : P ^ ℓ = 1 := by rw [← KVAux.nsmulPt_eq_pow]; exact hℓ
    have hN' : P ^ N = 1 := by rw [← KVAux.nsmulPt_eq_pow]; exact hN
    have hcop : Nat.gcd ℓ N = 1 := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓN
    have := pow_gcd_eq_one.mpr ⟨hℓ', hN'⟩
    rw [hcop, pow_one] at this
    exact this
  · exact hfin
  ·
    infer_instance
  · exact hlfp
  · exact hrank
  · exact hfibre
  ·
    intro T t P
    exact hker t P
  ·
    refine ⟨φ, hφ, ψ, hψ, φ_hom, ψ_hom, φ_act, ψ_act, ?_, ?_, ?_⟩
    · intro hℓ
      constructor
      ·
        have key := hψφ E.f ⟨𝟙 E.A, Category.id_comp _⟩
        rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E h1 ℓ hℓ] at key
        have := congrArg Subtype.val key
        simp only [mapPt_coe, Category.id_comp] at this
        exact this
      · have key := hφψ E'.f ⟨𝟙 E'.A, Category.id_comp _⟩
        rw [← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E' h1 ℓ hℓ] at key
        have := congrArg Subtype.val key
        simp only [mapPt_coe, Category.id_comp] at this
        exact this
    · intro T t P
      exact (hker t P).symm
    · intro T t P hP
      exact φ_lev t P hP

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_finrank_kernel_eq (solution)
