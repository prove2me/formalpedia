-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0606d975-8671-5012-93ea-ffa7420c0ece

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_UnramQuad_free_finrank_two_equalizer_frobenius_sq
import Theorems.Thm_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_monoidHom_aut_forall_q_eq_q_comp_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld.FormalOmega"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "FormalOmega.MumfordTower tree UnramQuad.free_finrank_two_equalizer_frobenius_sq UnramQuad.exists_frobenius_quotient_and_finite_flat_quotientMap FormalOmega.exists_finite_quotient_and_even_vdet_of_mem FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "MumfordTower Omega DeligneDatum DeligneDatum.IsPullback exists_finite_quotient_and_even_vdet_of_mem MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le"
namespace TwistedTowerAsm
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

section Rings
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

abbrev O2 : Type := ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))

abbrev On (n : ℕ) : Type := 𝒪 ⧸ Ideal.span {π ^ (n + 1)}

abbrev O2n (n : ℕ) : Type := O2 𝒪 Onr Fr ⧸ Ideal.span {(algebraMap 𝒪 (O2 𝒪 Onr Fr) π) ^ (n + 1)}

theorem le_comap (n : ℕ) :
    Ideal.span {π ^ (n + 1)} ≤ Ideal.comap (algebraMap 𝒪 (O2 𝒪 Onr Fr)) (Ideal.span {(algebraMap 𝒪 (O2 𝒪 Onr Fr) π) ^ (n + 1)}) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl

def qm (n : ℕ) : On 𝒪 π n →+* O2n 𝒪 π Onr Fr n :=
  Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 (O2 𝒪 Onr Fr) π) ^ (n + 1)}) (algebraMap 𝒪 (O2 𝒪 Onr Fr)) (le_comap 𝒪 π Onr Fr n)

def fac (n : ℕ) : On 𝒪 π (n + 1) →+* On 𝒪 π n :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))

def fac2 (n : ℕ) : O2n 𝒪 π Onr Fr (n + 1) →+* O2n 𝒪 π Onr Fr n :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (O2 𝒪 Onr Fr) π) (Nat.le_succ (n + 1))))

theorem square (n : ℕ) : (fac2 𝒪 π Onr Fr n).comp (qm 𝒪 π Onr Fr (n + 1)) = (qm 𝒪 π Onr Fr n).comp (fac 𝒪 π n) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

end Rings

section Tower
variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] {r : ℕ}
  {g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀} {N : Subgroup (PGL(2, K₀))}
  (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (D : MumfordTower 𝒪 π K₀ r g₁ N)

abbrev X (n : ℕ) : Scheme.{0} := pullback (D.zb n) (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)))
abbrev pr₁ (n : ℕ) : X Onr Fr D n ⟶ D.Z n := pullback.fst _ _
abbrev pr₂ (n : ℕ) : X Onr Fr D n ⟶ Spec (CommRingCat.of (O2n 𝒪 π Onr Fr n)) := pullback.snd _ _
abbrev xb (n : ℕ) : X Onr Fr D n ⟶ Spec (CommRingCat.of (On 𝒪 π n)) := pr₁ Onr Fr D n ≫ D.zb n

theorem specMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem xt_w (n : ℕ) :
    (pr₁ Onr Fr D n ≫ D.zt n) ≫ D.zb (n + 1) =
      (pr₂ Onr Fr D n ≫ Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n))) ≫
        Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr (n + 1))) := by
  rw [Category.assoc, (D.zt_isPullback n).w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
    ← specMap_comp', ← specMap_comp', square]
  rfl

def xt (n : ℕ) : X Onr Fr D n ⟶ X Onr Fr D (n + 1) :=
  pullback.lift (pr₁ Onr Fr D n ≫ D.zt n) (pr₂ Onr Fr D n ≫ Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n))) (xt_w Onr Fr D n)

@[scoped simp] theorem xt_pr₁ (n : ℕ) : xt Onr Fr D n ≫ pr₁ Onr Fr D (n + 1) = pr₁ Onr Fr D n ≫ D.zt n := pullback.lift_fst _ _ _
@[scoped simp] theorem xt_pr₂ (n : ℕ) :
    xt Onr Fr D n ≫ pr₂ Onr Fr D (n + 1) = pr₂ Onr Fr D n ≫ Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n)) :=
  pullback.lift_snd _ _ _

end Tower

section Transfer
variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] {r : ℕ}
  {g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀} {N : Subgroup (PGL(2, K₀))}
  (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (D : MumfordTower 𝒪 π K₀ r g₁ N)

theorem isFinite_pr₁ (n : ℕ) (hqfin : (qm 𝒪 π Onr Fr n).Finite) : IsFinite (pr₁ Onr Fr D n) := by
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n))) := (IsFinite.SpecMap_iff _).mpr hqfin
  infer_instance

theorem flat_pr₁ (n : ℕ) (hqflat : (qm 𝒪 π Onr Fr n).Flat) : Flat (pr₁ Onr Fr D n) := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n))) := Flat.SpecMap_iff.mpr hqflat
  infer_instance

theorem isProper_xb (n : ℕ) (hqfin : (qm 𝒪 π Onr Fr n).Finite) : IsProper (xb Onr Fr D n) := by
  haveI := isFinite_pr₁ Onr Fr D n hqfin
  haveI := D.zb_isProper n
  infer_instance

theorem flat_xb (n : ℕ) (hqflat : (qm 𝒪 π Onr Fr n).Flat) : Flat (xb Onr Fr D n) := by
  haveI := flat_pr₁ Onr Fr D n hqflat
  haveI := D.zb_flat n
  infer_instance

theorem affineNbhd_X (n : ℕ) (hqfin : (qm 𝒪 π Onr Fr n).Finite) (S : Set (X Onr Fr D n)) (hS : S.Finite) :
    ∃ U : (X Onr Fr D n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X Onr Fr D n)) := by
  haveI := isFinite_pr₁ Onr Fr D n hqfin
  obtain ⟨U, hU, hSU⟩ := D.affineNbhd n ((pr₁ Onr Fr D n).base '' S) (hS.image _)
  refine ⟨(pr₁ Onr Fr D n) ⁻¹ᵁ U, hU.preimage (pr₁ Onr Fr D n), ?_⟩
  intro x hx
  exact hSU ⟨x, hx, rfl⟩

end Transfer

section CoeffSquare
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

theorem ideal_map_eq (n : ℕ) :
    (Ideal.span {π ^ (n + 1)}).map (algebraMap 𝒪 (O2 𝒪 Onr Fr)) = Ideal.span {(algebraMap 𝒪 (O2 𝒪 Onr Fr) π) ^ (n + 1)} := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]

theorem isPushout_coeff (n : ℕ) :
    IsPushout (CommRingCat.ofHom (algebraMap 𝒪 (O2 𝒪 Onr Fr))) (CommRingCat.ofHom (algebraMap 𝒪 (On 𝒪 π n)))
      (CommRingCat.ofHom (algebraMap (O2 𝒪 Onr Fr) (O2n 𝒪 π Onr Fr n))) (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)) := by

  let e₁ : (O2 𝒪 Onr Fr ⧸ (Ideal.span {π ^ (n + 1)}).map (algebraMap 𝒪 (O2 𝒪 Onr Fr))) ≃ₐ[O2 𝒪 Onr Fr]
      (O2 𝒪 Onr Fr) ⊗[𝒪] (On 𝒪 π n) := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (O2 𝒪 Onr Fr) (Ideal.span {π ^ (n + 1)})
  let e₂ : (O2 𝒪 Onr Fr ⧸ (Ideal.span {π ^ (n + 1)}).map (algebraMap 𝒪 (O2 𝒪 Onr Fr))) ≃ₐ[O2 𝒪 Onr Fr] O2n 𝒪 π Onr Fr n :=
    Ideal.quotientEquivAlgOfEq (O2 𝒪 Onr Fr) (ideal_map_eq 𝒪 π Onr Fr n)
  let e : (O2 𝒪 Onr Fr) ⊗[𝒪] (On 𝒪 π n) ≃+* O2n 𝒪 π Onr Fr n := (e₁.symm.trans e₂).toRingEquiv
  refine (CommRingCat.isPushout_tensorProduct 𝒪 (O2 𝒪 Onr Fr) (On 𝒪 π n)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    e.toCommRingCatIso (by simp) (by simp) ?_ ?_
  ·
    ext b
    change e (b ⊗ₜ[𝒪] (1 : On 𝒪 π n)) = algebraMap (O2 𝒪 Onr Fr) (O2n 𝒪 π Onr Fr n) b
    change e₂ (e₁.symm (b ⊗ₜ[𝒪] (1 : On 𝒪 π n))) = _
    have : e₁.symm (b ⊗ₜ[𝒪] (1 : On 𝒪 π n)) = Ideal.Quotient.mk _ b := by
      rw [AlgEquiv.symm_apply_eq]; exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk _ _ b).symm
    rw [this]
    rfl
  ·
    ext a
    change e ((1 : O2 𝒪 Onr Fr) ⊗ₜ[𝒪] (Ideal.Quotient.mk _ a)) = qm 𝒪 π Onr Fr n (Ideal.Quotient.mk _ a)
    change e₂ (e₁.symm ((1 : O2 𝒪 Onr Fr) ⊗ₜ[𝒪] (Ideal.Quotient.mk _ a))) = _
    have : e₁.symm ((1 : O2 𝒪 Onr Fr) ⊗ₜ[𝒪] (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) a)) =
        Ideal.Quotient.mk _ (algebraMap 𝒪 (O2 𝒪 Onr Fr) a) := by
      rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rfl
    rw [this]
    rfl

theorem isPullback_coeff (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (O2 𝒪 Onr Fr) (O2n 𝒪 π Onr Fr n))))
      (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (O2 𝒪 Onr Fr)))) (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (On 𝒪 π n)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_coeff 𝒪 π Onr Fr n)

theorem isPullback_coeff_trans (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n))) (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)))
      (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr (n + 1)))) (Spec.map (CommRingCat.ofHom (fac 𝒪 π n))) := by
  have big := isPullback_coeff 𝒪 π Onr Fr n
  have right := isPullback_coeff 𝒪 π Onr Fr (n + 1)

  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap (O2 𝒪 Onr Fr) (O2n 𝒪 π Onr Fr n))) =
      Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (O2 𝒪 Onr Fr) (O2n 𝒪 π Onr Fr (n + 1)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have h₂ : Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (On 𝒪 π n))) =
      Spec.map (CommRingCat.ofHom (fac 𝒪 π n)) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (On 𝒪 π (n + 1)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  rw [h₁, h₂] at big
  exact IsPullback.of_right big (by rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, square]) right

end CoeffSquare

section Cartesian
variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] {r : ℕ}
  {g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀} {N : Subgroup (PGL(2, K₀))}
  (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (D : MumfordTower 𝒪 π K₀ r g₁ N)

theorem isPullback_X (n : ℕ) :
    IsPullback (pr₁ Onr Fr D n) (pr₂ Onr Fr D n) (D.zb n) (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n))) :=
  IsPullback.of_hasPullback _ _

theorem isPullback_xt_pr₂ (n : ℕ) :
    IsPullback (xt Onr Fr D n) (pr₂ Onr Fr D n) (pr₂ Onr Fr D (n + 1)) (Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n))) := by
  have outer : IsPullback (pr₁ Onr Fr D n ≫ D.zt n) (pr₂ Onr Fr D n) (D.zb (n + 1))
      (Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)) ≫ Spec.map (CommRingCat.ofHom (fac 𝒪 π n))) :=
    (isPullback_X Onr Fr D n).paste_horiz (D.zt_isPullback n)
  have e1 : pr₁ Onr Fr D n ≫ D.zt n = xt Onr Fr D n ≫ pr₁ Onr Fr D (n + 1) := (xt_pr₁ Onr Fr D n).symm
  have e2 : Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)) ≫ Spec.map (CommRingCat.ofHom (fac 𝒪 π n)) =
      Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n)) ≫ Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr (n + 1))) := by
    rw [← specMap_comp', ← specMap_comp', square]
  rw [e1, e2] at outer
  exact IsPullback.of_right outer (xt_pr₂ Onr Fr D n) (isPullback_X Onr Fr D (n + 1))

theorem isPullback_xt (n : ℕ) :
    IsPullback (xt Onr Fr D n) (xb Onr Fr D n) (xb Onr Fr D (n + 1)) (Spec.map (CommRingCat.ofHom (fac 𝒪 π n))) := by
  have h := (isPullback_xt_pr₂ Onr Fr D n).paste_vert (isPullback_coeff_trans 𝒪 π Onr Fr n)
  have e : ∀ m : ℕ, pr₂ Onr Fr D m ≫ Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr m)) = xb Onr Fr D m :=
    fun m => pullback.condition.symm
  rw [e, e] at h
  exact h

end Cartesian

section Twist
variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] {r : ℕ}
  {g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀} {N : Subgroup (PGL(2, K₀))}
  (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (D : MumfordTower 𝒪 π K₀ r g₁ N)

def specEquivIso {A : Type} [CommRing A] (e : A ≃+* A) : Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of A) where
  hom := Spec.map (CommRingCat.ofHom e.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : e.toRingHom.comp e.symm.toRingHom = RingHom.id A := by ext x; simp
    rw [this, CommRingCat.ofHom_id]; exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by ext x; simp
    rw [this, CommRingCat.ofHom_id]; exact Spec.map_id _

@[scoped simp] theorem specEquivIso_hom {A : Type} [CommRing A] (e : A ≃+* A) :
    (specEquivIso e).hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

theorem inv_comp_eq_of_hom_comp_eq {C : Type*} [Category C] {X Y : C} (α : X ≅ X) (f : X ⟶ Y) (h : α.hom ≫ f = f) :
    α.inv ≫ f = f := by
  rw [← h, ← Category.assoc, α.inv_hom_id, Category.id_comp, h]

def twist (n : ℕ) (α : D.Z n ≅ D.Z n) (hα : α.hom ≫ D.zb n = D.zb n)
    (β : Spec (CommRingCat.of (O2n 𝒪 π Onr Fr n)) ≅ Spec (CommRingCat.of (O2n 𝒪 π Onr Fr n)))
    (hβ : β.hom ≫ Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)) = Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n))) :
    X Onr Fr D n ≅ X Onr Fr D n where
  hom := pullback.lift (pr₁ Onr Fr D n ≫ α.hom) (pr₂ Onr Fr D n ≫ β.hom)
    (by rw [Category.assoc, hα, Category.assoc, hβ, pullback.condition])
  inv := pullback.lift (pr₁ Onr Fr D n ≫ α.inv) (pr₂ Onr Fr D n ≫ β.inv)
    (by rw [Category.assoc, inv_comp_eq_of_hom_comp_eq α _ hα, Category.assoc, inv_comp_eq_of_hom_comp_eq β _ hβ,
      pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, α.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, β.hom_inv_id,
        Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, α.inv_hom_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, β.inv_hom_id,
        Category.comp_id, Category.id_comp]

variable {Onr Fr D} in
@[scoped simp] theorem twist_hom_pr₁ (n : ℕ) (α : D.Z n ≅ D.Z n) (hα : α.hom ≫ D.zb n = D.zb n)
    (β : Spec (CommRingCat.of (O2n 𝒪 π Onr Fr n)) ≅ Spec (CommRingCat.of (O2n 𝒪 π Onr Fr n))) (hβ) :
    (twist Onr Fr D n α hα β hβ).hom ≫ pr₁ Onr Fr D n = pr₁ Onr Fr D n ≫ α.hom := pullback.lift_fst _ _ _

variable {Onr Fr D} in
@[scoped simp] theorem twist_hom_pr₂ (n : ℕ) (α : D.Z n ≅ D.Z n) (hα : α.hom ≫ D.zb n = D.zb n)
    (β : Spec (CommRingCat.of (O2n 𝒪 π Onr Fr n)) ≅ Spec (CommRingCat.of (O2n 𝒪 π Onr Fr n))) (hβ) :
    (twist Onr Fr D n α hα β hβ).hom ≫ pr₂ Onr Fr D n = pr₂ Onr Fr D n ≫ β.hom := pullback.lift_snd _ _ _

variable {Onr Fr D} in

theorem X_hom_ext (n : ℕ) {W : Scheme.{0}} (f g : W ⟶ X Onr Fr D n) (h₁ : f ≫ pr₁ Onr Fr D n = g ≫ pr₁ Onr Fr D n)
    (h₂ : f ≫ pr₂ Onr Fr D n = g ≫ pr₂ Onr Fr D n) : f = g := pullback.hom_ext h₁ h₂

end Twist

section Frob
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
  (Fr₂ : ∀ n : ℕ, O2n 𝒪 π Onr Fr n ≃ₐ[𝒪] O2n 𝒪 π Onr Fr n)
  (hind : ∀ (n : ℕ) (y y' : O2 𝒪 Onr Fr), (y' : Onr) = Fr (y : Onr) → Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
  (hinv : ∀ (n : ℕ) (x : O2n 𝒪 π Onr Fr n), Fr₂ n (Fr₂ n x) = x)
include hinv

theorem frob_sq (n : ℕ) : Fr₂ n * Fr₂ n = 1 := by
  ext x; exact hinv n x

theorem frob_zpow_of_even (n : ℕ) (k : ℤ) (hk : Even k) : Fr₂ n ^ k = 1 := by
  obtain ⟨m, rfl⟩ := hk
  rw [← two_mul, zpow_mul, zpow_two, frob_sq 𝒪 π Onr Fr Fr₂ hinv, one_zpow]

theorem frob_zpow_of_odd (n : ℕ) (k : ℤ) (hk : Odd k) : Fr₂ n ^ k = Fr₂ n := by
  obtain ⟨m, rfl⟩ := hk
  rw [zpow_add, zpow_one, zpow_mul, zpow_two, frob_sq 𝒪 π Onr Fr Fr₂ hinv, one_zpow, one_mul]

omit hinv in

theorem algEquiv_comp_qm (n : ℕ) (ψ : O2n 𝒪 π Onr Fr n ≃ₐ[𝒪] O2n 𝒪 π Onr Fr n) :
    ψ.toRingEquiv.toRingHom.comp (qm 𝒪 π Onr Fr n) = qm 𝒪 π Onr Fr n := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  change ψ (qm 𝒪 π Onr Fr n (Ideal.Quotient.mk _ a)) = qm 𝒪 π Onr Fr n (Ideal.Quotient.mk _ a)
  have : qm 𝒪 π Onr Fr n (Ideal.Quotient.mk _ a) = algebraMap 𝒪 (O2n 𝒪 π Onr Fr n) a := rfl
  rw [this, AlgEquiv.commutes]

omit hinv in
theorem specEquivIso_comp_qm (n : ℕ) (ψ : O2n 𝒪 π Onr Fr n ≃ₐ[𝒪] O2n 𝒪 π Onr Fr n) :
    (specEquivIso ψ.toRingEquiv).hom ≫ Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)) =
      Spec.map (CommRingCat.ofHom (qm 𝒪 π Onr Fr n)) := by
  rw [specEquivIso_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp, algEquiv_comp_qm]

include hind in
omit hinv in

theorem fac2_frob (n : ℕ) (x : O2n 𝒪 π Onr Fr (n + 1)) :
    fac2 𝒪 π Onr Fr n (Fr₂ (n + 1) x) = Fr₂ n (fac2 𝒪 π Onr Fr n x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x

  have hy : Fr (y : Onr) ∈ AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr) := by
    have h := y.2
    rw [AlgHom.mem_equalizer] at h ⊢
    change Fr (Fr (Fr (y : Onr))) = Fr (y : Onr)
    change Fr (Fr (y : Onr)) = (y : Onr) at h
    rw [h]
  let y' : O2 𝒪 Onr Fr := ⟨Fr (y : Onr), hy⟩
  rw [hind (n + 1) y y' rfl]
  change Ideal.Quotient.mk _ y' = Fr₂ n (Ideal.Quotient.mk _ y)
  rw [hind n y y' rfl]

include hind in
theorem fac2_comp_frob_zpow (n : ℕ) (k : ℤ) :
    (fac2 𝒪 π Onr Fr n).comp (Fr₂ (n + 1) ^ k).toRingEquiv.toRingHom =
      (Fr₂ n ^ k).toRingEquiv.toRingHom.comp (fac2 𝒪 π Onr Fr n) := by
  rcases Int.even_or_odd k with hk | hk
  · rw [frob_zpow_of_even 𝒪 π Onr Fr Fr₂ hinv _ k hk, frob_zpow_of_even 𝒪 π Onr Fr Fr₂ hinv _ k hk]
    ext x
    change fac2 𝒪 π Onr Fr n ((1 : O2n 𝒪 π Onr Fr (n + 1) ≃ₐ[𝒪] O2n 𝒪 π Onr Fr (n + 1)) x) =
      (1 : O2n 𝒪 π Onr Fr n ≃ₐ[𝒪] O2n 𝒪 π Onr Fr n) (fac2 𝒪 π Onr Fr n x)
    rw [AlgEquiv.one_apply, AlgEquiv.one_apply]
  · rw [frob_zpow_of_odd 𝒪 π Onr Fr Fr₂ hinv _ k hk, frob_zpow_of_odd 𝒪 π Onr Fr Fr₂ hinv _ k hk]
    ext x
    change fac2 𝒪 π Onr Fr n (Fr₂ (n + 1) x) = Fr₂ n (fac2 𝒪 π Onr Fr n x)
    exact fac2_frob 𝒪 π Onr Fr Fr₂ hind n x

end Frob

section Lift
variable {A B C : Type} [Group A] [Group B] [Group C]

noncomputable def liftSurj (θ : A →* B) (hθ : Function.Surjective θ) (f : A →* C) (hker : ∀ a, θ a = 1 → f a = 1) :
    B →* C where
  toFun b := f (Classical.choose (hθ b))
  map_one' := hker _ (Classical.choose_spec (hθ 1))
  map_mul' b b' := by
    have h : θ ((Classical.choose (hθ b) * Classical.choose (hθ b'))⁻¹ * Classical.choose (hθ (b * b'))) = 1 := by
      rw [map_mul, map_inv, map_mul, Classical.choose_spec (hθ b), Classical.choose_spec (hθ b'),
        Classical.choose_spec (hθ (b * b')), inv_mul_cancel]
    have := hker _ h
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    rw [← this, map_mul]

theorem liftSurj_apply (θ : A →* B) (hθ : Function.Surjective θ) (f : A →* C) (hker : ∀ a, θ a = 1 → f a = 1) (a : A) :
    liftSurj θ hθ f hker (θ a) = f a := by
  change f (Classical.choose (hθ (θ a))) = f a
  have h : θ ((Classical.choose (hθ (θ a)))⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, Classical.choose_spec (hθ (θ a)), inv_mul_cancel]
  have := hker _ h
  rwa [map_mul, map_inv, inv_mul_eq_one] at this

end Lift

section Action
variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] {r : ℕ}
  {g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀} {N : Subgroup (PGL(2, K₀))}
  (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (D : MumfordTower 𝒪 π K₀ r g₁ N)
  (Fr₂ : ∀ n : ℕ, O2n 𝒪 π Onr Fr n ≃ₐ[𝒪] O2n 𝒪 π Onr Fr n)
  {G : Type} [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
  (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
  (act : ∀ n : ℕ, ↥Γ →* Aut (D.Z n)) (hover : ∀ (n : ℕ) (γ : ↥Γ), (act n γ).hom ≫ D.zb n = D.zb n)

def expo (γ : ↥Γ) : ℤ := - Multiplicative.toAdd (vdet (σ (γ : G)))

theorem expo_mul (γ δ : ↥Γ) : expo σ Γ vdet (γ * δ) = expo σ Γ vdet δ + expo σ Γ vdet γ := by
  simp only [expo, Subgroup.coe_mul, map_mul, toAdd_mul]; ring

theorem specMap_algEquiv_mul (n : ℕ) (ϕ ψ : O2n 𝒪 π Onr Fr n ≃ₐ[𝒪] O2n 𝒪 π Onr Fr n) :
    Spec.map (CommRingCat.ofHom (ϕ * ψ).toRingEquiv.toRingHom) =
      Spec.map (CommRingCat.ofHom ϕ.toRingEquiv.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψ.toRingEquiv.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

def bAut (n : ℕ) (γ : ↥Γ) : X Onr Fr D n ≅ X Onr Fr D n :=
  twist Onr Fr D n (act n γ) (hover n γ) (specEquivIso (Fr₂ n ^ expo σ Γ vdet γ).toRingEquiv)
    (specEquivIso_comp_qm 𝒪 π Onr Fr n _)

theorem bAut_hom_pr₁ (n : ℕ) (γ : ↥Γ) :
    (bAut Onr Fr D Fr₂ σ Γ vdet act hover n γ).hom ≫ pr₁ Onr Fr D n = pr₁ Onr Fr D n ≫ (act n γ).hom :=
  twist_hom_pr₁ _ _ _ _ _

theorem bAut_hom_pr₂ (n : ℕ) (γ : ↥Γ) :
    (bAut Onr Fr D Fr₂ σ Γ vdet act hover n γ).hom ≫ pr₂ Onr Fr D n =
      pr₂ Onr Fr D n ≫ Spec.map (CommRingCat.ofHom (Fr₂ n ^ expo σ Γ vdet γ).toRingEquiv.toRingHom) :=
  twist_hom_pr₂ _ _ _ _ _

def bHom (n : ℕ) : ↥Γ →* Aut (X Onr Fr D n) where
  toFun := bAut Onr Fr D Fr₂ σ Γ vdet act hover n
  map_one' := by
    apply Iso.ext
    apply X_hom_ext
    · rw [bAut_hom_pr₁, map_one]; change pr₁ Onr Fr D n ≫ 𝟙 _ = 𝟙 _ ≫ pr₁ Onr Fr D n; simp
    · rw [bAut_hom_pr₂]
      have : expo σ Γ vdet (1 : ↥Γ) = 0 := by simp [expo]
      rw [this, zpow_zero]
      change pr₂ Onr Fr D n ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _ ≫ pr₂ Onr Fr D n
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]
  map_mul' γ δ := by
    apply Iso.ext
    change (bAut Onr Fr D Fr₂ σ Γ vdet act hover n (γ * δ)).hom =
      (bAut Onr Fr D Fr₂ σ Γ vdet act hover n δ).hom ≫ (bAut Onr Fr D Fr₂ σ Γ vdet act hover n γ).hom
    apply X_hom_ext
    · rw [bAut_hom_pr₁, Category.assoc, bAut_hom_pr₁, ← Category.assoc, bAut_hom_pr₁, Category.assoc, map_mul]; rfl
    · rw [bAut_hom_pr₂, Category.assoc, bAut_hom_pr₂, ← Category.assoc, bAut_hom_pr₂, Category.assoc, expo_mul, zpow_add,
        specMap_algEquiv_mul]

theorem bHom_apply (n : ℕ) (γ : ↥Γ) : bHom Onr Fr D Fr₂ σ Γ vdet act hover n γ = bAut Onr Fr D Fr₂ σ Γ vdet act hover n γ := rfl

theorem bHom_eq_one (hinv : ∀ (n : ℕ) (x : O2n 𝒪 π Onr Fr n), Fr₂ n (Fr₂ n x) = x) (n : ℕ) (γ : ↥Γ)
    (h₁ : (act n γ).hom = 𝟙 (D.Z n)) (h₂ : Even (Multiplicative.toAdd (vdet (σ (γ : G))))) :
    bHom Onr Fr D Fr₂ σ Γ vdet act hover n γ = 1 := by
  apply Iso.ext
  apply X_hom_ext
  · rw [bHom_apply, bAut_hom_pr₁, h₁]; change pr₁ Onr Fr D n ≫ 𝟙 _ = 𝟙 _ ≫ pr₁ Onr Fr D n; simp
  · rw [bHom_apply, bAut_hom_pr₂, frob_zpow_of_even 𝒪 π Onr Fr Fr₂ hinv n _ (by simpa [expo] using h₂.neg)]
    change pr₂ Onr Fr D n ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _ ≫ pr₂ Onr Fr D n
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]

end Action

end CerednikDrinfeld.FormalOmega.TwistedTowerAsm
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld.FormalOmega.TwistedTowerAsm"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld.FormalOmega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld"

open CerednikDrinfeld.FormalOmega.TwistedTowerAsm in
theorem solution

    {r : ℕ} [Fact r.Prime]
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
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0)
    (DM : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
      (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
      (G₂ : Type) (_ : Group G₂) (_ : Finite G₂) (a : ∀ n : ℕ, G₂ →* Aut (X n))
      (pr₁ : ∀ n : ℕ, X n ⟶ DM.Z n) (pr₂ : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
      (θ : ↥Γ →* G₂) (Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})),

      (∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1)) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))) ∧
      (∀ n : ℕ, IsProper (xb n)) ∧ (∀ n : ℕ, Flat (xb n)) ∧
      (∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n))) ∧
      (∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xb n = xb n) ∧
      (∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom) ∧

      (∀ n : ℕ, IsPullback (pr₁ n) (pr₂ n) (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))) ∧
      (∀ n : ℕ, xb n = pr₁ n ≫ DM.zb n) ∧
      (∀ n : ℕ, xt n ≫ pr₁ (n + 1) = pr₁ n ≫ DM.zt n) ∧
      (∀ n : ℕ, xt n ≫ pr₂ (n + 1) = pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1))))))) ∧

      Function.Surjective θ ∧ (∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N) ∧

      (∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
        Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y') ∧

      (∀ (n : ℕ) (γ : ↥Γ), (a n (θ γ)).hom ≫ pr₂ n =
        pr₂ n ≫ Spec.map (CommRingCat.ofHom ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom)) ∧

      (∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
        ∀ x : Spec (CommRingCat.of B) ⟶ X n, x ≫ pr₁ n = DM.q n B hB P → (x ≫ (a n (θ γ)).hom) ≫ pr₁ n = DM.q n B hB P') := by
  classical
  obtain ⟨hfree, hrank, -, -, -⟩ := CerednikDrinfeld.UnramQuad.free_finrank_two_equalizer_frobenius_sq 𝒪 hdvr π hπ hcomplete hres hunr
    K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr
  obtain ⟨Fr₂, hind, hinv, hff⟩ :=
    CerednikDrinfeld.UnramQuad.exists_frobenius_quotient_and_finite_flat_quotientMap 𝒪 π Onr Fr hfree hrank
  obtain ⟨G₂, grp, fin, θ, hθs, hθk, hpar⟩ :=
    CerednikDrinfeld.FormalOmega.exists_finite_quotient_and_even_vdet_of_mem 𝒪 hdvr π hπ K₀ vdet hvdet G σ Γ Γ' hΓ' ρ hρ
      N hNle hNnorm hNidx
  have hΓ'le : Γ' ≤ Γ := fun x hx => ((hΓ' x).mp hx).1
  have hNleΓ : N ≤ Γ.map ρ := hNle.trans (Subgroup.map_mono hΓ'le)
  obtain ⟨act, hover, hzt, htriv, hq⟩ :=
    CerednikDrinfeld.FormalOmega.MumfordTower.exists_monoidHom_aut_forall_q_eq_q_comp_of_le 𝒪 π K₀ r g₁ G σ Γ ρ hρ N
      hNleΓ hNnorm DM
  letI := grp
  let a : ∀ n : ℕ, G₂ →* Aut (X Onr Fr DM n) := fun n =>
    liftSurj θ hθs (bHom Onr Fr DM Fr₂ σ Γ vdet act hover n)
      (fun γ hγ => bHom_eq_one Onr Fr DM Fr₂ σ Γ vdet act hover hinv n γ (htriv n γ ((hθk γ).mp hγ))
        (hpar γ ((hθk γ).mp hγ)))
  have ha : ∀ (n : ℕ) (γ : ↥Γ), a n (θ γ) = bAut Onr Fr DM Fr₂ σ Γ vdet act hover n γ := fun n γ =>
    liftSurj_apply θ hθs _ _ γ
  refine ⟨X Onr Fr DM, xb Onr Fr DM, xt Onr Fr DM, G₂, grp, fin, a, pr₁ Onr Fr DM, pr₂ Onr Fr DM, θ, Fr₂,
    isPullback_xt Onr Fr DM, fun n => isProper_xb Onr Fr DM n (hff n).1, fun n => flat_xb Onr Fr DM n (hff n).2,
    fun n S hS => affineNbhd_X Onr Fr DM n (hff n).1 S hS, ?_, ?_, isPullback_X Onr Fr DM, fun n => rfl,
    xt_pr₁ Onr Fr DM, xt_pr₂ Onr Fr DM, hθs, hθk, hind, ?_, ?_⟩
  ·
    intro n g
    obtain ⟨γ, rfl⟩ := hθs g
    rw [ha]
    change (bAut Onr Fr DM Fr₂ σ Γ vdet act hover n γ).hom ≫ pr₁ Onr Fr DM n ≫ DM.zb n = pr₁ Onr Fr DM n ≫ DM.zb n
    rw [← Category.assoc, bAut_hom_pr₁, Category.assoc, hover]
  ·
    intro n g
    obtain ⟨γ, rfl⟩ := hθs g
    rw [ha, ha]
    apply X_hom_ext
    · have e1 : ((bAut Onr Fr DM Fr₂ σ Γ vdet act hover n γ).hom ≫ xt Onr Fr DM n) ≫ pr₁ Onr Fr DM (n + 1) =
          pr₁ Onr Fr DM n ≫ DM.zt n ≫ (act (n + 1) γ).hom := by
        rw [Category.assoc, xt_pr₁, ← Category.assoc, bAut_hom_pr₁, Category.assoc, ← hzt]
      have e2 : (xt Onr Fr DM n ≫ (bAut Onr Fr DM Fr₂ σ Γ vdet act hover (n + 1) γ).hom) ≫ pr₁ Onr Fr DM (n + 1) =
          pr₁ Onr Fr DM n ≫ DM.zt n ≫ (act (n + 1) γ).hom := by
        rw [Category.assoc, bAut_hom_pr₁, ← Category.assoc, xt_pr₁, Category.assoc]
      exact e1.trans e2.symm
    · have e1 : ((bAut Onr Fr DM Fr₂ σ Γ vdet act hover n γ).hom ≫ xt Onr Fr DM n) ≫ pr₂ Onr Fr DM (n + 1) =
          pr₂ Onr Fr DM n ≫ (Spec.map (CommRingCat.ofHom (Fr₂ n ^ expo σ Γ vdet γ).toRingEquiv.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n))) := by
        rw [Category.assoc, xt_pr₂, ← Category.assoc, bAut_hom_pr₂, Category.assoc]
      have e2 : (xt Onr Fr DM n ≫ (bAut Onr Fr DM Fr₂ σ Γ vdet act hover (n + 1) γ).hom) ≫ pr₂ Onr Fr DM (n + 1) =
          pr₂ Onr Fr DM n ≫ (Spec.map (CommRingCat.ofHom (fac2 𝒪 π Onr Fr n)) ≫
            Spec.map (CommRingCat.ofHom (Fr₂ (n + 1) ^ expo σ Γ vdet γ).toRingEquiv.toRingHom)) := by
        rw [Category.assoc, bAut_hom_pr₂, ← Category.assoc, xt_pr₂, Category.assoc]
      rw [e1, e2, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        fac2_comp_frob_zpow 𝒪 π Onr Fr Fr₂ hind hinv]
  ·
    intro n γ
    rw [ha, bAut_hom_pr₂]
    rfl
  ·
    intro n γ B _ _ hB P P' hPP' x hx
    rw [ha, Category.assoc, bAut_hom_pr₁, ← Category.assoc, hx]
    exact (hq n γ B hB P P' hPP').symm

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower.CerednikDrinfeld.FormalOmega.TwistedTowerAsm"

end S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower (solution)
