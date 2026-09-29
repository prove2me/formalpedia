-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_linearMap_forall_apply_eq_pushPt_act
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/aa8bcf69-0cb9-549a-a376-738bc4a2544e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Theorems.Thm_TateModule_exists_linearMap_forall_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_linearMap_forall_apply_eq_pushPt_act

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

open scoped Quaternion

noncomputable section

namespace FecTateAction

variable {k : Type} [CommRing k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} {Ω : Type} [CommRing Ω] [Algebra k Ω]

def pushHom (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f),
      pushPt φ hφ (L.mul _ P Q) = L.mul _ (pushPt φ hφ P) (pushPt φ hφ Q)) :
    L.AlgPoints hc Ω →+ L.AlgPoints hc Ω :=
  AddMonoidHom.mk' (fun Q => RelativeGroupLaw.AlgPoints.ofPoint (pushPt φ hφ (RelativeGroupLaw.AlgPoints.toPoint Q)))
    fun P Q => by
      apply RelativeGroupLaw.AlgPoints.toPoint_injective
      rw [RelativeGroupLaw.AlgPoints.toPoint_ofPoint, RelativeGroupLaw.AlgPoints.toPoint_add,
        RelativeGroupLaw.AlgPoints.toPoint_add, RelativeGroupLaw.AlgPoints.toPoint_ofPoint,
        RelativeGroupLaw.AlgPoints.toPoint_ofPoint]
      exact hhom _ _

theorem toPoint_pushHom (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f),
      pushPt φ hφ (L.mul _ P Q) = L.mul _ (pushPt φ hφ P) (pushPt φ hφ Q)) (Q : L.AlgPoints hc Ω) :
    RelativeGroupLaw.AlgPoints.toPoint (pushHom L hc φ hφ hhom Q) =
      pushPt φ hφ (RelativeGroupLaw.AlgPoints.toPoint Q) := rfl

theorem tateModule_ext {p : ℕ} {M : Type} [AddCommGroup M] {x y : TateModule p M}
    (h : ∀ n : ℕ, (x : ℕ → M) n = (y : ℕ → M) n) : x = y :=
  Subtype.ext (funext h)

end FecTateAction

end

open FecTateAction in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {K : Type} [Field K] (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ ρ : ↥Λ → (TateModule ℓ (E.L.AlgPoints E.comm Ω) →ₗ[ℤ_[ℓ]] TateModule ℓ (E.L.AlgPoints E.comm Ω)),
      (∀ (m : ↥Λ) (v : TateModule ℓ (E.L.AlgPoints E.comm Ω)) (n : ℕ),
        RelativeGroupLaw.AlgPoints.toPoint ((ρ m v : ℕ → E.L.AlgPoints E.comm Ω) n) =
          pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((v : ℕ → E.L.AlgPoints E.comm Ω) n))) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id) ∧
      (∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
        ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m ∘ₗ ρ m') ∧
      (∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m') := by
  classical

  let φ : ↥Λ → (E.L.AlgPoints E.comm Ω →+ E.L.AlgPoints E.comm Ω) := fun m =>
    pushHom E.L E.comm (E.act m) (E.act_over m) (fun P Q => E.act_hom m _ P Q)
  have hT : ∀ m : ↥Λ, ∃ T : TateModule ℓ (E.L.AlgPoints E.comm Ω) →ₗ[ℤ_[ℓ]] TateModule ℓ (E.L.AlgPoints E.comm Ω),
      ∀ (x : TateModule ℓ (E.L.AlgPoints E.comm Ω)) (n : ℕ),
        ((T x : TateModule ℓ (E.L.AlgPoints E.comm Ω)) : ℕ → E.L.AlgPoints E.comm Ω) n =
          φ m ((x : ℕ → E.L.AlgPoints E.comm Ω) n) :=
    fun m => TateModule.exists_linearMap_forall_apply_eq ℓ _ _ (φ m)
  choose ρ hρ using hT
  have hρ' : ∀ (m : ↥Λ) (v : TateModule ℓ (E.L.AlgPoints E.comm Ω)) (n : ℕ),
      RelativeGroupLaw.AlgPoints.toPoint ((ρ m v : ℕ → E.L.AlgPoints E.comm Ω) n) =
        pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((v : ℕ → E.L.AlgPoints E.comm Ω) n)) := by
    intro m v n
    rw [hρ]
    rfl

  have hval : ∀ (m : ↥Λ) (v : TateModule ℓ (E.L.AlgPoints E.comm Ω)) (n : ℕ),
      (RelativeGroupLaw.AlgPoints.toPoint ((ρ m v : ℕ → E.L.AlgPoints E.comm Ω) n)).1 =
        (RelativeGroupLaw.AlgPoints.toPoint ((v : ℕ → E.L.AlgPoints E.comm Ω) n)).1 ≫ E.act m := by
    intro m v n
    rw [hρ']
    rfl
  refine ⟨ρ, hρ', ?_, ?_, ?_⟩
  ·
    intro h1
    refine LinearMap.ext fun v => tateModule_ext fun n => ?_
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    apply Subtype.ext
    rw [hval, E.act_one h1, Category.comp_id, LinearMap.id_apply]
  ·
    intro m m' h
    refine LinearMap.ext fun v => tateModule_ext fun n => ?_
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    apply Subtype.ext
    rw [hval, E.act_mul m m' h, LinearMap.comp_apply, hval, hval, Category.assoc]
  ·
    intro m m'
    refine LinearMap.ext fun v => tateModule_ext fun n => ?_
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    rw [hρ', E.act_add, LinearMap.add_apply, TateModule.coe_add, Pi.add_apply, RelativeGroupLaw.AlgPoints.toPoint_add,
      hρ', hρ']

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_linearMap_forall_apply_eq_pushPt_act
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_linearMap_forall_apply_eq_pushPt_act (solution)
