-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.OmegaNr.forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e24e4376-6571-578f-b3a7-eed3289e7c8d

import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_OmegaNr_forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace P2mExtend

def relPairs {𝒪 : Type} [CommRing 𝒪] (F : AlgFunctor 𝒪)
    (R : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], F.obj B → F.obj B → Prop)
    (hR : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
      (x x' : F.obj B), R B x x' → R B' (F.map φ x) (F.map φ x')) : AlgFunctor 𝒪 where
  obj B _ _ := {p : F.obj B × F.obj B // R B p.1 p.2}
  map φ p := ⟨(F.map φ p.1.1, F.map φ p.1.2), hR _ _ φ _ _ p.2⟩
  map_id p := by
    apply Subtype.ext
    change (F.map _ p.1.1, F.map _ p.1.2) = p.1
    rw [F.map_id, F.map_id]
  map_comp f g p := by
    apply Subtype.ext
    change (F.map (g.comp f) p.1.1, F.map (g.comp f) p.1.2) = (F.map g (F.map f p.1.1), F.map g (F.map f p.1.2))
    rw [F.map_comp, F.map_comp]

end P2mExtend

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (hF : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      ∀ x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      ∃ (S : Subalgebra 𝒪 B) (_ : IsNoetherianRing ↥S) (x₀ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S),
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val x₀ = x)
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (u₁ u₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fN).obj B)
    (hu₁ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
      (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      u₁ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (u₁ B hB x))
    (hu₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
      (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      u₂ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (u₂ B hB x))

    (hrel : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)),
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → u₁ B hB x' = u₂ B hB x) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → u₁ B hB x' = u₂ B hB x := by
  obtain ⟨hfun, htot, -, -, hnat, -⟩ := CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws π Onr Fr vdet
  intro B _ _ hB x x' hxx'
  exact AlgebraicGeometry.Scheme.nilpPoints.forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem π
    (P2mExtend.relPairs (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π))
      (fun B _ _ y y' => OmegaNr.IsTwistedAct π Onr Fr vdet B g y y')
      (fun B _ _ B' _ _ φ y y' h => hnat B B' φ g y y' h))
    fN
    (fun B _ _ hB p => by
      obtain ⟨S, hSN, y₀, hy⟩ := hF B hB p.1.1
      obtain ⟨y₀', hy₀'⟩ := htot ↥S g y₀
      have h' : p.1.2 = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val y₀' :=
        hfun B g p.1.1 _ _ p.2 (hy ▸ hnat ↥S B S.val g y₀ y₀' hy₀')
      exact ⟨S, hSN, ⟨(y₀, y₀'), hy₀'⟩, Subtype.ext (Prod.ext hy h'.symm)⟩)
    (fun B _ _ hB p => u₁ B hB p.1.2) (fun B _ _ hB p => u₂ B hB p.1.1)
    (fun B _ _ B' _ _ hB hB' φ p => hu₁ B B' hB hB' φ p.1.2)
    (fun B _ _ B' _ _ hB hB' φ p => hu₂ B B' hB hB' φ p.1.1)
    (fun B _ _ _ hB hc p => hrel B hB hc p.1.1 p.1.2 p.2)
    B hB ⟨(x, x'), hxx'⟩

end S_CerednikDrinfeld_FormalOmega_OmegaNr_forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_OmegaNr_forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem (solution)
