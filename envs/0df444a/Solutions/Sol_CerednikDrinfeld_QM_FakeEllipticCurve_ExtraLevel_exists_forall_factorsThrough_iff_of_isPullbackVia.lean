-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/995f4102-2f56-56fd-b7ad-d75277c36630

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

open CategoryTheory.Limits GoodReductionJacobian

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) (n : ℕ) (K : E.ExtraLevel n) :
    ∃ K' : E'.ExtraLevel n,
      ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
        FactorsThrough K'.levK P ↔
          FactorsThrough K.levK (t := t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.1.w, ← Category.assoc, P.2]⟩ := by
  classical
  obtain ⟨hg, hmul, hact, hlev⟩ := hg

  have hσ := fun {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) =>
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback φ E E' g hg
      (fun t P Q => hmul t P Q) hact t

  let C' : Scheme.{0} := pullback K.levK g
  let lev' : C' ⟶ E'.A := pullback.snd K.levK g

  have hpts : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      FactorsThrough lev' P ↔
        FactorsThrough K.levK (t := t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ := by
    intro T t' P
    constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨P₀ ≫ pullback.fst K.levK g, ?_⟩
      show (P₀ ≫ pullback.fst K.levK g) ≫ K.levK = P.1 ≫ g
      rw [Category.assoc, pullback.condition, ← Category.assoc, hP₀]
    · rintro ⟨P₀, hP₀⟩
      exact ⟨pullback.lift P₀ P.1 hP₀, pullback.lift_snd _ _ _⟩

  have hsq : IsPullback (pullback.fst K.levK g) (lev' ≫ E'.f) (K.levK ≫ E.f) (Spec.map (CommRingCat.ofHom φ)) :=
    (IsPullback.of_hasPullback K.levK g).paste_vert hg

  have key : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S'))
      (σ : SchemeHomOver t' E'.f ≃ SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f)
      (hσ1 : ∀ P : SchemeHomOver t' E'.f, (σ P).1 = P.1 ≫ g) (P : SchemeHomOver t' E'.f),
      FactorsThrough lev' P ↔ FactorsThrough K.levK (σ P) := by
    intro T t' σ hσ1 P
    rw [hpts t' P]
    unfold FactorsThrough
    rw [hσ1]
  haveI := K.levK_closed
  haveI : IsClosedImmersion lev' := inferInstanceAs (IsClosedImmersion (pullback.snd K.levK g))
  haveI := K.levK_finite
  haveI := K.levK_flat
  haveI := K.levK_finitePresentation
  refine ⟨{ K := C'
            levK := lev'
            levK_closed := ‹IsClosedImmersion lev'›
            levK_sub := ?_
            levK_one := ?_
            levK_torsion := ?_
            levK_stable := ?_
            levK_disjoint := ?_
            levK_finite := MorphismProperty.of_isPullback hsq K.levK_finite
            levK_flat := MorphismProperty.of_isPullback hsq K.levK_flat
            levK_finitePresentation := MorphismProperty.of_isPullback hsq K.levK_finitePresentation
            levK_rank := ?_
            levK_fibre := ?_ }, fun t' P => hpts t' P⟩
  ·
    intro T t' P Q hP hQ
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ := hσ t'
    obtain ⟨h1, h2⟩ := K.levK_sub _ (σ P) (σ Q) ((key t' σ hσ1 P).mp hP) ((key t' σ hσ1 Q).mp hQ)
    constructor
    · rw [key t' σ hσ1, hσmul]; exact h1
    · rw [key t' σ hσ1, hσinv]; exact h2
  ·
    intro T t'
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ := hσ t'
    rw [key t' σ hσ1, hσone]
    exact K.levK_one _
  ·
    intro T t' P hP
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ := hσ t'
    apply σ.injective
    rw [hσnsmul, hσone]
    exact K.levK_torsion _ (σ P) ((key t' σ hσ1 P).mp hP)
  ·
    intro x T t' P hP
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ := hσ t'
    rw [key t' σ hσ1, hσact]
    exact K.levK_stable x _ (σ P) ((key t' σ hσ1 P).mp hP)
  ·
    intro T t' P hK hl
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ := hσ t'
    apply σ.injective
    rw [hσone]
    apply K.levK_disjoint _ (σ P) ((key t' σ hσ1 P).mp hK)
    obtain ⟨P₀, hP₀⟩ := hlev t' P hl
    exact ⟨P₀, by rw [hP₀, hσ1]⟩
  ·
    intro s
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq]
    exact K.levK_rank _
  ·
    intro k _ _ sk hn
    obtain ⟨σ, hσ1, hσone, hσmul, hσinv, hσnsmul, hσact⟩ := hσ (geomPoint k sk)
    have hgeom : geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (sk.comp φ) := by
      simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h0 := K.levK_fibre k (sk.comp φ) hn
    rw [← hgeom] at h0
    obtain ⟨e₀, he₀⟩ := h0
    let σsub : {P : SchemeHomOver (geomPoint k sk) E'.f // FactorsThrough lev' P} ≃
        {Q : SchemeHomOver (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ)) E.f // FactorsThrough K.levK Q} :=
      σ.subtypeEquiv (fun P => key _ σ hσ1 P)
    have hσsub : ∀ z, ((σsub.symm z : {P : SchemeHomOver (geomPoint k sk) E'.f // FactorsThrough lev' P}) :
        SchemeHomOver (geomPoint k sk) E'.f) = σ.symm z.1 := fun _ => rfl
    have hσsymm : ∀ u v : SchemeHomOver (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom φ)) E.f,
        σ.symm (E.L.mul _ u v) = E'.L.mul (geomPoint k sk) (σ.symm u) (σ.symm v) := by
      intro u v
      apply σ.injective
      rw [Equiv.apply_symm_apply, hσmul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨e₀.trans σsub.symm, fun x y => ?_⟩
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, hσsub, hσsub, hσsub, he₀, hσsymm]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia (solution)
