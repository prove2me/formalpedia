-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f6d0aa02-9631-576d-b3d9-8f88b98b458d

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace G2Body

def toSPoint (R : Type) [CommRing R] (π : R) (q : ℕ) (S : Type) [CommRing S] [Algebra R S]
    (T : Type) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (x : (chartE R π q).obj T) : (chartE S (algebraMap R S π) q).obj T :=
  ⟨x.1, by
    obtain ⟨h₁, h₂, h₃⟩ := x.2
    refine ⟨?_, h₂, h₃⟩
    rw [h₁, IsScalarTower.algebraMap_apply R S T]⟩

theorem algHom_ext (R : Type) [CommRing R] (π : R) (q : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (f g : chartERing R π q →ₐ[R] B) (hξ : f (chartERing.ξ R π q) = g (chartERing.ξ R π q))
    (hη : f (chartERing.η R π q) = g (chartERing.η R π q)) : f = g :=
  (chartERing.corepEquiv R π q B).injective (Subtype.ext (Prod.ext hξ hη))

end G2Body

open G2Body in
theorem solution
    (R : Type) [CommRing R] (π : R) (q : ℕ) (S : Type) [CommRing S] [Algebra R S] :
    ∃ φ : chartERing R π q →+* chartERing S (algebraMap R S π) q,
      φ.comp (algebraMap R (chartERing R π q)) = (algebraMap S (chartERing S (algebraMap R S π) q)).comp (algebraMap R S) ∧
      φ (chartERing.ξ R π q) = chartERing.ξ S (algebraMap R S π) q ∧
      φ (chartERing.η R π q) = chartERing.η S (algebraMap R S π) q ∧
      IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R (chartERing R π q)))
        (CommRingCat.ofHom (algebraMap S (chartERing S (algebraMap R S π) q))) (CommRingCat.ofHom φ) ∧
      ∀ φ' : chartERing R π q →+* chartERing S (algebraMap R S π) q,
        φ'.comp (algebraMap R (chartERing R π q)) = (algebraMap S (chartERing S (algebraMap R S π) q)).comp (algebraMap R S) →
        φ' (chartERing.ξ R π q) = chartERing.ξ S (algebraMap R S π) q →
        φ' (chartERing.η R π q) = chartERing.η S (algebraMap R S π) q → φ' = φ := by
  classical

  letI algRAS : Algebra R (chartERing S (algebraMap R S π) q) :=
    ((algebraMap S (chartERing S (algebraMap R S π) q)).comp (algebraMap R S)).toAlgebra
  haveI istRS : IsScalarTower R S (chartERing S (algebraMap R S π) q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let pt : (chartE R π q).obj (chartERing S (algebraMap R S π) q) :=
    ⟨(chartERing.ξ S (algebraMap R S π) q, chartERing.η S (algebraMap R S π) q), by
      refine ⟨?_, (chartERing.point S (algebraMap R S π) q).2.2.1, (chartERing.point S (algebraMap R S π) q).2.2.2⟩
      rw [chartERing.ξ_mul_η]
      rfl⟩
  let φa : chartERing R π q →ₐ[R] chartERing S (algebraMap R S π) q := chartERing.lift pt
  have hφξ : φa (chartERing.ξ R π q) = chartERing.ξ S (algebraMap R S π) q := chartERing.lift_ξ pt
  have hφη : φa (chartERing.η R π q) = chartERing.η S (algebraMap R S π) q := chartERing.lift_η pt
  have hcomp : φa.toRingHom.comp (algebraMap R (chartERing R π q)) =
      (algebraMap S (chartERing S (algebraMap R S π) q)).comp (algebraMap R S) := by
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    rfl
  refine ⟨φa.toRingHom, hcomp, hφξ, hφη, ?_, ?_⟩
  ·
    letI algAA : Algebra (chartERing R π q) (chartERing S (algebraMap R S π) q) := φa.toRingHom.toAlgebra
    haveI istRAA : IsScalarTower R (chartERing R π q) (chartERing S (algebraMap R S π) q) :=
      IsScalarTower.of_algebraMap_eq (fun r => (φa.commutes r).symm)
    haveI hP : Algebra.IsPushout R (chartERing R π q) S (chartERing S (algebraMap R S π) q) := by
      refine Algebra.isPushout_of_forall_existsUnique_algHom_comp_eq (fun T _ _ g hg => ?_)
      letI algRT : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
      haveI istRST : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

      let ga : chartERing R π q →ₐ[R] T :=
        { toRingHom := g
          commutes' := fun r => by
            have := congrArg (fun f : R →+* T => f r) hg
            simp only [RingHom.coe_comp, Function.comp_apply] at this
            exact this }
      let x : (chartE R π q).obj T := chartERing.corepEquiv R π q T ga
      let k : chartERing S (algebraMap R S π) q →ₐ[S] T := chartERing.lift (toSPoint R π q S T x)
      have hkξ : k (chartERing.ξ S (algebraMap R S π) q) = g (chartERing.ξ R π q) := chartERing.lift_ξ _
      have hkη : k (chartERing.η S (algebraMap R S π) q) = g (chartERing.η R π q) := chartERing.lift_η _
      refine ⟨k, ?_, ?_⟩
      ·
        have : (k.restrictScalars R).comp φa = ga := by
          apply algHom_ext R π q
          · show k (φa (chartERing.ξ R π q)) = g (chartERing.ξ R π q)
            rw [hφξ, hkξ]
          · show k (φa (chartERing.η R π q)) = g (chartERing.η R π q)
            rw [hφη, hkη]
        exact congrArg AlgHom.toRingHom this
      · intro k' hk'
        apply (chartERing.corepEquiv S (algebraMap R S π) q T).injective
        apply Subtype.ext
        apply Prod.ext
        · show k' (chartERing.ξ S (algebraMap R S π) q) = k (chartERing.ξ S (algebraMap R S π) q)
          rw [hkξ, ← hφξ]
          exact congrArg (fun f : chartERing R π q →+* T => f (chartERing.ξ R π q)) hk'
        · show k' (chartERing.η S (algebraMap R S π) q) = k (chartERing.η S (algebraMap R S π) q)
          rw [hkη, ← hφη]
          exact congrArg (fun f : chartERing R π q →+* T => f (chartERing.η R π q)) hk'
    haveI := hP.symm
    exact CommRingCat.isPushout_of_isPushout R S (chartERing R π q) (chartERing S (algebraMap R S π) q)
  ·
    intro φ' h1 h2 h3
    let φ'a : chartERing R π q →ₐ[R] chartERing S (algebraMap R S π) q :=
      { toRingHom := φ'
        commutes' := fun r => by
          have := congrArg (fun f : R →+* chartERing S (algebraMap R S π) q => f r) h1
          simp only [RingHom.coe_comp, Function.comp_apply] at this
          exact this }
    have : φ'a = φa := algHom_ext R π q φ'a φa (h2.trans hφξ.symm) (h3.trans hφη.symm)
    exact congrArg AlgHom.toRingHom this

end S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange (solution)
