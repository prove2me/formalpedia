-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/12bcb5d9-5b14-57ff-89de-6c026c7ac3ea

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S : Type u} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ N m S)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (K : Type u) [Field K] [IsAlgClosed K] (ι : k →+* K)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ) :
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u.2.P k sk))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u.2.P k sk)) = u.1.L.one (geomPoint k sk)) ↔
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint K (ι.comp sk)) n (FakeEllipticCurve.sectionAt u.2.P K (ι.comp sk)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint K (ι.comp sk)) n (FakeEllipticCurve.sectionAt u.2.P K (ι.comp sk))) = u.1.L.one (geomPoint K (ι.comp sk))) := by
  have hσ : Spec.map (CommRingCat.ofHom ι) ≫ geomPoint k sk = geomPoint K (ι.comp sk) := by
    simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let H : SchemeHomOver (geomPoint k sk) u.1.f → SchemeHomOver (geomPoint K (ι.comp sk)) u.1.f :=
    fun Q => schemeHomOverComp (Spec.map (CommRingCat.ofHom ι)) hσ Q
  have H_coe : ∀ Q, (H Q).1 = Spec.map (CommRingCat.ofHom ι) ≫ Q.1 := fun _ => rfl

  haveI : Surjective (Spec.map (CommRingCat.ofHom ι)) :=
    ⟨fun p => ⟨(inferInstance : Inhabited ↥(Spec (CommRingCat.of K))).default, Subsingleton.elim _ _⟩⟩
  haveI : IsSeparated u.1.f := u.1.bundle.proper.toIsSeparated
  have H_inj : Function.Injective H := by
    intro Q Q' hQ
    apply Subtype.ext
    exact ext_of_isDominant_of_isSeparated u.1.f (by rw [Q.2, Q'.2]) (Spec.map (CommRingCat.ofHom ι))
      (congrArg Subtype.val hQ)
  have H_mul : ∀ P Q, H (u.1.L.mul _ P Q) = u.1.L.mul _ (H P) (H Q) := fun P Q =>
    u.1.L.mul_natural _ _ _ hσ P Q
  have H_one : H (u.1.L.one _) = u.1.L.one _ := u.1.L.one_natural _ _ _ hσ
  have H_nsmul : ∀ (j : ℕ) Q, H (nsmulPt u.1.L _ j Q) = nsmulPt u.1.L _ j (H Q) := by
    intro j Q
    induction j with
    | zero => exact H_one
    | succ j ih =>
      show H (u.1.L.mul _ (nsmulPt u.1.L _ j Q) Q) = u.1.L.mul _ (nsmulPt u.1.L _ j (H Q)) (H Q)
      rw [H_mul, ih]
  have H_act : ∀ (x : ↥Λ) Q, H (pushPt (u.1.act x) (u.1.act_over x) Q) = pushPt (u.1.act x) (u.1.act_over x) (H Q) := by
    intro x Q
    apply Subtype.ext
    simp only [H_coe, pushPt, mapPt_coe, Category.assoc]
  have H_sec : H (FakeEllipticCurve.sectionAt u.2.P k sk) = FakeEllipticCurve.sectionAt u.2.P K (ι.comp sk) := by
    apply Subtype.ext
    simp only [H_coe, FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, ← Category.assoc, hσ]

  have H_lev : ∀ Q, FactorsThrough u.1.lev (H Q) → FactorsThrough u.1.lev Q := by
    intro Q ⟨P₀, hP₀⟩
    haveI := u.1.lev_closed
    let l : Spec (CommRingCat.of K) ⟶ Limits.pullback Q.1 u.1.lev :=
      Limits.pullback.lift (Spec.map (CommRingCat.ofHom ι)) P₀ (by rw [hP₀, H_coe])
    haveI : Surjective (Limits.pullback.fst Q.1 u.1.lev) :=
      ⟨fun p => ⟨l.base (inferInstance : Inhabited ↥(Spec (CommRingCat.of K))).default, Subsingleton.elim _ _⟩⟩
    haveI : IsIso (Limits.pullback.fst Q.1 u.1.lev) := isIso_of_isClosedImmersion_of_surjective _
    refine ⟨inv (Limits.pullback.fst Q.1 u.1.lev) ≫ Limits.pullback.snd Q.1 u.1.lev, ?_⟩
    rw [Category.assoc, ← Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  have key : ∀ x : ↥Λ,
      H (pushPt (u.1.act x) (u.1.act_over x)
        (nsmulPt u.1.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt u.2.P k sk))) =
      pushPt (u.1.act x) (u.1.act_over x)
        (nsmulPt u.1.L (geomPoint K (ι.comp sk)) n (FakeEllipticCurve.sectionAt u.2.P K (ι.comp sk))) := by
    intro x; rw [H_act, H_nsmul, H_sec]
  constructor
  · intro Hc x hx hfac
    have hfac' := H_lev _ ((key x).symm ▸ hfac)
    have h1 := Hc x hx hfac'
    rw [← key x, h1, H_one]
  · intro Hc x hx hfac
    obtain ⟨P₀, hP₀⟩ := hfac
    have hfac' : FactorsThrough u.1.lev (pushPt (u.1.act x) (u.1.act_over x)
        (nsmulPt u.1.L (geomPoint K (ι.comp sk)) n (FakeEllipticCurve.sectionAt u.2.P K (ι.comp sk)))) :=
      ⟨Spec.map (CommRingCat.ofHom ι) ≫ P₀, by rw [Category.assoc, hP₀, ← H_coe, key x]⟩
    have h1 := Hc x hx hfac'
    apply H_inj
    rw [key x, h1, H_one]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_ringHom (solution)
