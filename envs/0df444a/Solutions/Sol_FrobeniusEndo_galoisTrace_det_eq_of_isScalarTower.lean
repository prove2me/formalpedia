-- Prove2me | solution 1 for FrobeniusEndo.galoisTrace_det_eq_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d5aa3883-a41f-52b2-bbd0-00ebbf23314f

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_galoisTrace_det_eq_of_isScalarTower

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem solution {R : Type*} [CommRing R] {F : Type*} [Field F]
    {k : Type*} [Field k] [DecidableEq k] {K : Type*} [Field K] [DecidableEq K]
    [Algebra R F] [Algebra R k] [Algebra R K] [Algebra F k] [Algebra F K] [Algebra k K]
    [IsScalarTower R F k] [IsScalarTower R F K] [IsScalarTower F k K]
    (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (τ : K ≃ₐ[F] K)
    (hστ : ∀ x : k, τ (algebraMap k K x) = algebraMap k K (σ x))
    (p : ℕ) [Fact p.Prime]
    (hk : Nat.card (Submodule.torsionBy ℤ (W⁄k).Point p) = p ^ 2)
    (hK : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) :
    galoisTrace F W p σ = galoisTrace F W p τ ∧
      LinearMap.det (galoisRepModuleEnd F W p σ) = LinearMap.det (galoisRepModuleEnd F W p τ) := by

  set f : k →ₐ[F] K := IsScalarTower.toAlgHom F k K with hf
  set ι : (W⁄k).Point →+ (W⁄K).Point := Point.map f with hι
  have hιinj : Function.Injective ι := Point.map_injective f

  have hcomp : f.comp σ.toAlgHom = τ.toAlgHom.comp f := by
    apply AlgHom.ext
    intro x
    show algebraMap k K (σ x) = τ (algebraMap k K x)
    exact (hστ x).symm
  have hιeq : ∀ P : (W⁄k).Point, ι (σ • P) = τ • ι P := by
    intro P
    rw [algEquiv_smul_def, algEquiv_smul_def, hι, Point.map_map, Point.map_map, hcomp]

  set Tk := Submodule.torsionBy ℤ (W⁄k).Point p with hTk
  set TK := Submodule.torsionBy ℤ (W⁄K).Point p with hTK
  have hmem : ∀ x : Tk, ι (x : (W⁄k).Point) ∈ TK := by
    intro x
    have hx : (p : ℤ) • (x : (W⁄k).Point) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rw [hTK, Submodule.mem_torsionBy_iff]
    show (p : ℤ) • ι (x : (W⁄k).Point) = 0
    rw [← map_zsmul ι, hx, _root_.map_zero]
  let gₐ : Tk →+ TK :=
    { toFun := fun x => ⟨ι x, hmem x⟩
      map_zero' := Subtype.ext (_root_.map_zero ι)
      map_add' := fun x y => Subtype.ext (_root_.map_add ι _ _) }
  let g : Tk →ₗ[ZMod p] TK := gₐ.toZModLinearMap p
  have hg_apply : ∀ x : Tk, ((g x : TK) : (W⁄K).Point) = ι x := fun x => rfl
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hιinj
    have := congrArg (fun z : TK => (z : (W⁄K).Point)) hxy
    simpa [hg_apply] using this
  haveI : Finite TK := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  have hgbij : Function.Bijective g := hginj.bijective_of_nat_card_le (by rw [hk, hK])
  let e : Tk ≃ₗ[ZMod p] TK := LinearEquiv.ofBijective g hgbij
  have he_apply : ∀ x : Tk, ((e x : TK) : (W⁄K).Point) = ι x := fun x => rfl

  have hconj : galoisRepModuleEnd F W p τ
      = (e : Tk →ₗ[ZMod p] TK) ∘ₗ galoisRepModuleEnd F W p σ ∘ₗ (e.symm : TK →ₗ[ZMod p] Tk) := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
      galoisRepModuleEnd_apply]
    apply Subtype.ext
    show τ • ((e x : TK) : (W⁄K).Point) = ((e (σ • x) : TK) : (W⁄K).Point)
    rw [he_apply, he_apply]
    exact (hιeq x).symm
  refine ⟨?_, ?_⟩
  · rw [galoisTrace_def, galoisTrace_def, hconj]
    exact (LinearMap.trace_conj' (galoisRepModuleEnd F W p σ) e).symm
  · rw [hconj]
    exact (LinearMap.det_conj (galoisRepModuleEnd F W p σ) e).symm

end S_FrobeniusEndo_galoisTrace_det_eq_of_isScalarTower
end P2MW
export P2MW.S_FrobeniusEndo_galoisTrace_det_eq_of_isScalarTower (solution)
