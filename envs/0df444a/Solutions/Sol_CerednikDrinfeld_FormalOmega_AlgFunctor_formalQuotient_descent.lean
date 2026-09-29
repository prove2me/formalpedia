-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.AlgFunctor.formalQuotient_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1356621f-5a18-58ad-825c-a135e7271e6d

import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)

    (Γ : Type) [Group Γ] (act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → F.obj B → F.obj B → Prop)
    (hact_fun : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x x' x'' : F.obj B), act B γ x x' → act B γ x x'' → x' = x'')
    (hact_total : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x : F.obj B), ∃ x', act B γ x x')
    (hact_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : F.obj B), act B 1 x x)
    (hact_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ γ' : Γ) (x y z : F.obj B), act B γ x y → act B γ' y z → act B (γ' * γ) x z)
    (hact_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (γ : Γ)
      (x x' : F.obj B), act B γ x x' → act B' γ (F.map φ x) (F.map φ x'))
    (Γ' : Subgroup Γ)

    (𝒳' 𝒳 : Scheme.{0}) (f' : 𝒳' ⟶ Spec (CommRingCat.of 𝒪)) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (p : 𝒳' ⟶ 𝒳) (hp : p ≫ f = f')
    (a : Γ → (𝒳' ⟶ 𝒳')) (ha_over : ∀ γ, a γ ≫ f' = f') (ha_p : ∀ γ, a γ ≫ p = p) (ha_one : ∀ γ ∈ Γ', a γ = 𝟙 𝒳')
    (ha_mul : ∀ γ γ' : Γ, a (γ' * γ) = a γ ≫ a γ')

    (hp_univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), ρ B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (y : (Scheme.nilpPoints f').obj B),
        ρ B hB ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y) = ρ B hB y) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B),
          u B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y) = ρ B hB y) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B),
            u' B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y) = ρ B hB y) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = u B hB z)

    (Θ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints f').obj B)
    (hΘ'_nat : (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), Θ' B' hB' (F.map φ x) = (Scheme.nilpPoints f').map φ (Θ' B hB x)))
    (hΘ'_eqv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' →
      Θ' B hB x' = (Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B (Θ' B hB x))
    (hΘ'_univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), ρ B' hB' (F.map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ), γ ∈ Γ' → ∀ x x' : F.obj B, act B γ x x' → ρ B hB x' = ρ B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), u B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u B hB (Θ' B hB x) = ρ B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f').obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f').obj B), u' B' hB' ((Scheme.nilpPoints f').map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u' B hB (Θ' B hB x) = ρ B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B), u' B hB y = u B hB y)
    :

    let Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints f).obj B := fun B _ _ hB x => (Scheme.nilpPoints.mapHom f' f p hp).app B (Θ' B hB x)
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), Θ B' hB' (F.map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x)) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' → Θ B hB x' = Θ B hB x) ∧
    (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : F.obj B), ρ B' hB' (F.map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B), act B γ x x' → ρ B hB x' = ρ B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u B hB (Θ B hB x) = ρ B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints f).obj B), u' B' hB' ((Scheme.nilpPoints f).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : F.obj B), u' B hB (Θ B hB x) = ρ B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints f).obj B), u' B hB z = u B hB z) := by
  intro Θ

  have pa : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (y : (Scheme.nilpPoints f').obj B),
      (Scheme.nilpPoints.mapHom f' f p hp).app B ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y) =
        (Scheme.nilpPoints.mapHom f' f p hp).app B y := by
    intro B _ _ γ y
    apply Subtype.ext
    show (y.1 ≫ a γ) ≫ p = y.1 ≫ p
    rw [Category.assoc, ha_p]
  have pnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
      (y : (Scheme.nilpPoints f').obj B),
      (Scheme.nilpPoints.mapHom f' f p hp).app B' ((Scheme.nilpPoints f').map φ y) =
        (Scheme.nilpPoints f).map φ ((Scheme.nilpPoints.mapHom f' f p hp).app B y) := by
    intro B _ _ B' _ _ φ y
    apply Subtype.ext
    show (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ y.1) ≫ p = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (y.1 ≫ p)
    rw [Category.assoc]
  have anat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (γ : Γ)
      (y : (Scheme.nilpPoints f').obj B),
      (Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B' ((Scheme.nilpPoints f').map φ y) =
        (Scheme.nilpPoints f').map φ ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y) := by
    intro B _ _ B' _ _ φ γ y
    apply Subtype.ext
    show (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ y.1) ≫ a γ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (y.1 ≫ a γ)
    rw [Category.assoc]
  have aa : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ γ' : Γ) (y : (Scheme.nilpPoints f').obj B),
      (Scheme.nilpPoints.mapHom f' f' (a γ') (ha_over γ')).app B ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y) =
        (Scheme.nilpPoints.mapHom f' f' (a (γ' * γ)) (ha_over (γ' * γ))).app B y := by
    intro B _ _ γ γ' y
    apply Subtype.ext
    show (y.1 ≫ a γ) ≫ a γ' = y.1 ≫ a (γ' * γ)
    rw [Category.assoc, ha_mul]

  have hnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : F.obj B), Θ B' hB' (F.map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x) := by
    intro B _ _ B' _ _ hB hB' φ x
    show (Scheme.nilpPoints.mapHom f' f p hp).app B' (Θ' B' hB' (F.map φ x)) = _
    rw [hΘ'_nat B B' hB hB' φ x, pnat]

  have hinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : F.obj B),
      act B γ x x' → Θ B hB x' = Θ B hB x := by
    intro B _ _ hB γ x x' hxx'
    show (Scheme.nilpPoints.mapHom f' f p hp).app B (Θ' B hB x') = (Scheme.nilpPoints.mapHom f' f p hp).app B (Θ' B hB x)
    rw [hΘ'_eqv B hB γ x x' hxx', pa]
  refine ⟨hnat, hinv, ?_⟩
  ·
    intro T t ρ hρnat hρinv

    obtain ⟨u', hu'nat, hu'fac, hu'uniq⟩ := hΘ'_univ T t ρ hρnat (fun B _ _ hB γ _ x x' h => hρinv B hB γ x x' h)

    have hu'inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ)
        (y : (Scheme.nilpPoints f').obj B),
        u' B hB ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y) = u' B hB y := by
      intro B _ _ hB γ y

      have key := hu'uniq (fun B _ _ hB y => u' B hB ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B y))
        (by
          intro B _ _ B' _ _ hB hB' φ x
          show u' B' hB' ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B' ((Scheme.nilpPoints f').map φ x)) = _
          rw [anat, hu'nat])
        (by
          intro B _ _ hB x
          obtain ⟨x', hx'⟩ := hact_total B γ x
          show u' B hB ((Scheme.nilpPoints.mapHom f' f' (a γ) (ha_over γ)).app B (Θ' B hB x)) = ρ B hB x
          rw [← hΘ'_eqv B hB γ x x' hx', hu'fac, hρinv B hB γ x x' hx'])
      exact key B hB y

    obtain ⟨u, hunat, hufac, huuniq⟩ := hp_univ T t u' hu'nat hu'inv
    refine ⟨u, hunat, fun B _ _ hB x => ?_, ?_⟩
    · show u B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B (Θ' B hB x)) = ρ B hB x
      rw [hufac, hu'fac]
    · intro u'' hu''nat hu''fac B _ _ hB z

      have h1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f').obj B),
          u'' B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y) = u' B hB y :=
        hu'uniq (fun B _ _ hB y => u'' B hB ((Scheme.nilpPoints.mapHom f' f p hp).app B y))
          (by
            intro B _ _ B' _ _ hB hB' φ x
            show u'' B' hB' ((Scheme.nilpPoints.mapHom f' f p hp).app B' ((Scheme.nilpPoints f').map φ x)) = _
            rw [pnat, hu''nat])
          (fun B _ _ hB x => hu''fac B hB x)
      exact huuniq u'' hu''nat h1 B hB z

end S_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent (solution)
