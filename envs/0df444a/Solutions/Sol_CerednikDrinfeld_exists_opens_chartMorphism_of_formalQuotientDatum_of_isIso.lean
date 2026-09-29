-- Prove2me | solution 1 for CerednikDrinfeld.exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1b5c67a7-9e25-5a1a-9312-d79136d9df9c

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace P2mWs2K5b

theorem appLE_congr_hom {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

theorem id_appLE {X : Scheme} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) : (𝟙 X : X ⟶ X).appLE U U e = 𝟙 _ := by
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app, show (homOfLE e).op = 𝟙 (Opposite.op U) from rfl]
  erw [X.presheaf.map_id, Category.comp_id]

theorem transport_sq {Y₁ Y₂ X₁ X₂ : Scheme.{0}} (jnr : Y₁ ⟶ Y₂) (jn : X₁ ⟶ X₂) (E₁ : Y₁ ≅ X₁) (E₂ : Y₂ ≅ X₂)
    (hEj : jnr ≫ E₂.hom = E₁.hom ≫ jn) (U₁ : Y₁.Opens) (U₂ : Y₂.Opens)
    (hUle₁ : U₁ ≤ E₁.hom ⁻¹ᵁ (E₁.inv ⁻¹ᵁ U₁)) (hUle₂ : U₂ ≤ E₂.hom ⁻¹ᵁ (E₂.inv ⁻¹ᵁ U₂))
    (hle : E₁.inv ⁻¹ᵁ U₁ ≤ jn ⁻¹ᵁ (E₂.inv ⁻¹ᵁ U₂)) (hle₀ : U₁ ≤ jnr ⁻¹ᵁ U₂) :
    jn.app (E₂.inv ⁻¹ᵁ U₂) ≫ X₁.presheaf.map (homOfLE hle).op ≫ E₁.hom.appLE (E₁.inv ⁻¹ᵁ U₁) U₁ hUle₁ =
      E₂.hom.appLE (E₂.inv ⁻¹ᵁ U₂) U₂ hUle₂ ≫ jnr.app U₂ ≫ Y₁.presheaf.map (homOfLE hle₀).op := by
  simp only [Scheme.Hom.app_eq_appLE]
  rw [← Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom hEj.symm _ _ _ _

theorem transport_preimage {Y₁ Y₂ X₁ X₂ : Scheme.{0}} (jnr : Y₁ ⟶ Y₂) (jn : X₁ ⟶ X₂) (E₁ : Y₁ ≅ X₁) (E₂ : Y₂ ≅ X₂)
    (hEj : jnr ≫ E₂.hom = E₁.hom ≫ jn) (U₁ : Y₁.Opens) (U₂ : Y₂.Opens) (hU : U₁ = jnr ⁻¹ᵁ U₂) :
    E₁.inv ⁻¹ᵁ U₁ = jn ⁻¹ᵁ (E₂.inv ⁻¹ᵁ U₂) := by
  have hEj' : E₁.inv ≫ jnr = jn ≫ E₂.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hEj, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Scheme.Hom.comp_preimage, ← hEj', Scheme.Hom.comp_preimage, ← hU]

theorem transport_transitions {Y₁ Y₂ X₁ X₂ : Scheme.{0}} (jnr : Y₁ ⟶ Y₂) (jn : X₁ ⟶ X₂)
    (E₁ : Y₁ ≅ X₁) (E₂ : Y₂ ≅ X₂) (hEj : jnr ≫ E₂.hom = E₁.hom ≫ jn) (U₁ : Y₁.Opens) (U₂ : Y₂.Opens)
    (hUle₁ : U₁ ≤ E₁.hom ⁻¹ᵁ (E₁.inv ⁻¹ᵁ U₁)) (hUle₂ : U₂ ≤ E₂.hom ⁻¹ᵁ (E₂.inv ⁻¹ᵁ U₂))
    {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂]
    (c₁ : ↑(Y₁.presheaf.obj (Opposite.op U₁)) →+* A₁) (c₂ : ↑(Y₂.presheaf.obj (Opposite.op U₂)) →+* A₂)
    (fac : A₂ →+* A₁)
    (hU : U₁ = jnr ⁻¹ᵁ U₂ ∧ ∀ (hle : U₁ ≤ jnr ⁻¹ᵁ U₂) (s : ↑(Y₂.presheaf.obj (Opposite.op U₂))),
      c₁ (Y₁.presheaf.map (homOfLE hle).op ((jnr.app U₂).hom s)) = fac (c₂ s)) :
    E₁.inv ⁻¹ᵁ U₁ = jn ⁻¹ᵁ (E₂.inv ⁻¹ᵁ U₂) ∧
      ∀ (hle : E₁.inv ⁻¹ᵁ U₁ ≤ jn ⁻¹ᵁ (E₂.inv ⁻¹ᵁ U₂)) (s : ↑(X₂.presheaf.obj (Opposite.op (E₂.inv ⁻¹ᵁ U₂)))),
        (c₁.comp (E₁.hom.appLE (E₁.inv ⁻¹ᵁ U₁) U₁ hUle₁).hom)
            (X₁.presheaf.map (homOfLE hle).op ((jn.app (E₂.inv ⁻¹ᵁ U₂)).hom s)) =
          fac ((c₂.comp (E₂.hom.appLE (E₂.inv ⁻¹ᵁ U₂) U₂ hUle₂).hom) s) := by
  refine ⟨transport_preimage jnr jn E₁ E₂ hEj U₁ U₂ hU.1, fun hle s => ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply, ← hU.2 hU.1.le]
  congr 1
  have := congrArg (fun φ => φ.hom s) (transport_sq jnr jn E₁ E₂ hEj U₁ U₂ hUle₁ hUle₂ hle hU.1.le)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this

theorem transport_functions (Y X : ℕ → Scheme.{0}) (jnr : ∀ m : ℕ, Y m ⟶ Y (m + 1)) (jn : ∀ m : ℕ, X m ⟶ X (m + 1))
    (E : ∀ m : ℕ, Y m ≅ X m) (hEj : ∀ m : ℕ, jnr m ≫ (E (m + 1)).hom = (E m).hom ≫ jn m)
    (U : ∀ m : ℕ, (Y m).Opens) (hUj : ∀ m : ℕ, U m = (jnr m) ⁻¹ᵁ (U (m + 1)))
    (hUle : ∀ m : ℕ, U m ≤ (E m).hom ⁻¹ᵁ ((E m).inv ⁻¹ᵁ (U m)))
    (hUle' : ∀ m : ℕ, (E m).inv ⁻¹ᵁ (U m) ≤ (E m).inv ⁻¹ᵁ (U m))
    (A : ℕ → Type) [∀ m, CommRing (A m)] (c : ∀ m : ℕ, ↑((Y m).presheaf.obj (Opposite.op (U m))) →+* A m)
    {P Q : (∀ m : ℕ, A m) → Prop}
    (hF : (∀ (S S' : ∀ m : ℕ, ↑((Y m).presheaf.obj (Opposite.op (U m)))),
          (∀ (m : ℕ) (hle : U m ≤ (jnr m) ⁻¹ᵁ (U (m + 1))),
              (Y m).presheaf.map (homOfLE hle).op (((jnr m).app (U (m + 1))).hom (S (m + 1))) = S m) →
          (∀ (m : ℕ) (hle : U m ≤ (jnr m) ⁻¹ᵁ (U (m + 1))),
              (Y m).presheaf.map (homOfLE hle).op (((jnr m).app (U (m + 1))).hom (S' (m + 1))) = S' m) →
          (∀ m : ℕ, c m (S m) = c m (S' m)) → S = S') ∧
        ∀ fam : ∀ m : ℕ, A m, Q fam →
          ((∃ S : ∀ m : ℕ, ↑((Y m).presheaf.obj (Opposite.op (U m))),
              (∀ (m : ℕ) (hle : U m ≤ (jnr m) ⁻¹ᵁ (U (m + 1))),
                (Y m).presheaf.map (homOfLE hle).op (((jnr m).app (U (m + 1))).hom (S (m + 1))) = S m) ∧
              ∀ m : ℕ, c m (S m) = fam m) ↔ P fam)) :
    (∀ (s s' : ∀ m : ℕ, ↑((X m).presheaf.obj (Opposite.op ((E m).inv ⁻¹ᵁ (U m))))),
        (∀ (m : ℕ) (hle : (E m).inv ⁻¹ᵁ (U m) ≤ (jn m) ⁻¹ᵁ ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))),
            (X m).presheaf.map (homOfLE hle).op (((jn m).app ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))).hom (s (m + 1))) = s m) →
        (∀ (m : ℕ) (hle : (E m).inv ⁻¹ᵁ (U m) ≤ (jn m) ⁻¹ᵁ ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))),
            (X m).presheaf.map (homOfLE hle).op (((jn m).app ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))).hom (s' (m + 1))) = s' m) →
        (∀ m : ℕ, ((c m).comp ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom) (s m) =
          ((c m).comp ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom) (s' m)) → s = s') ∧
      ∀ fam : ∀ m : ℕ, A m, Q fam →
        ((∃ s : ∀ m : ℕ, ↑((X m).presheaf.obj (Opposite.op ((E m).inv ⁻¹ᵁ (U m)))),
            (∀ (m : ℕ) (hle : (E m).inv ⁻¹ᵁ (U m) ≤ (jn m) ⁻¹ᵁ ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))),
              (X m).presheaf.map (homOfLE hle).op (((jn m).app ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))).hom (s (m + 1))) = s m) ∧
            ∀ m : ℕ, ((c m).comp ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom) (s m) = fam m) ↔
          P fam) := by
  obtain ⟨Finj, Fiff⟩ := hF

  have hfb : ∀ m : ℕ, (E m).inv.appLE (U m) ((E m).inv ⁻¹ᵁ (U m)) (hUle' m) ≫
      (E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m) = 𝟙 _ := by
    intro m
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (E m).hom_inv_id (U m) (U m) _ le_rfl, id_appLE]
  have hbf : ∀ m : ℕ, (E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m) ≫
      (E m).inv.appLE (U m) ((E m).inv ⁻¹ᵁ (U m)) (hUle' m) = 𝟙 _ := by
    intro m
    rw [Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (E m).inv_hom_id ((E m).inv ⁻¹ᵁ (U m)) ((E m).inv ⁻¹ᵁ (U m)) _ le_rfl, id_appLE]
  have e1 : ∀ (m : ℕ) (x : ↑((X m).presheaf.obj (Opposite.op ((E m).inv ⁻¹ᵁ (U m))))),
      ((E m).inv.appLE (U m) ((E m).inv ⁻¹ᵁ (U m)) (hUle' m)).hom
        (((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom x) = x := by
    intro m x
    have := congrArg (fun φ => φ.hom x) (hbf m)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] using this
  have e2 : ∀ (m : ℕ) (y : ↑((Y m).presheaf.obj (Opposite.op (U m)))),
      ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom
        (((E m).inv.appLE (U m) ((E m).inv ⁻¹ᵁ (U m)) (hUle' m)).hom y) = y := by
    intro m y
    have := congrArg (fun φ => φ.hom y) (hfb m)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] using this
  have e3 : ∀ (m : ℕ) (hle : (E m).inv ⁻¹ᵁ (U m) ≤ (jn m) ⁻¹ᵁ ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1))))
      (hle₀ : U m ≤ (jnr m) ⁻¹ᵁ (U (m + 1))) (x : ↑((X (m + 1)).presheaf.obj (Opposite.op ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))))),
      ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom
        ((X m).presheaf.map (homOfLE hle).op (((jn m).app ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1)))).hom x)) =
      (Y m).presheaf.map (homOfLE hle₀).op (((jnr m).app (U (m + 1))).hom
        (((E (m + 1)).hom.appLE ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1))) (U (m + 1)) (hUle (m + 1))).hom x)) := by
    intro m hle hle₀ x
    have := congrArg (fun φ => φ.hom x)
      (transport_sq (jnr m) (jn m) (E m) (E (m + 1)) (hEj m) (U m) (U (m + 1)) (hUle m) (hUle (m + 1)) hle hle₀)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hle' : ∀ m : ℕ, (E m).inv ⁻¹ᵁ (U m) ≤ (jn m) ⁻¹ᵁ ((E (m + 1)).inv ⁻¹ᵁ (U (m + 1))) :=
    fun m => (transport_preimage (jnr m) (jn m) (E m) (E (m + 1)) (hEj m) (U m) (U (m + 1)) (hUj m)).le
  have hle₀' : ∀ m : ℕ, U m ≤ (jnr m) ⁻¹ᵁ (U (m + 1)) := fun m => (hUj m).le
  constructor
  · intro s s' hs hs' hc
    have key := Finj (fun m => ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom (s m))
      (fun m => ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom (s' m))
      (fun m hle₀ => by rw [← e3 m (hle' m) hle₀, hs m (hle' m)])
      (fun m hle₀ => by rw [← e3 m (hle' m) hle₀, hs' m (hle' m)])
      (fun m => by simpa only [RingHom.comp_apply] using hc m)
    funext m
    rw [← e1 m (s m), ← e1 m (s' m)]
    exact congrArg _ (congrFun key m)
  · intro fam hfam
    refine Iff.trans ?_ (Fiff fam hfam)
    constructor
    · rintro ⟨s, hs, hcs⟩
      refine ⟨fun m => ((E m).hom.appLE ((E m).inv ⁻¹ᵁ (U m)) (U m) (hUle m)).hom (s m), ?_, ?_⟩
      · intro m hle₀
        rw [← e3 m (hle' m) hle₀, hs m (hle' m)]
      · intro m
        simpa only [RingHom.comp_apply] using hcs m
    · rintro ⟨S, hS, hcS⟩
      refine ⟨fun m => ((E m).inv.appLE (U m) ((E m).inv ⁻¹ᵁ (U m)) (hUle' m)).hom (S m), ?_, ?_⟩
      · intro m hle
        refine (e1 m _).symm.trans ?_
        rw [e3 m hle (hle₀' m), e2, hS m (hle₀' m)]
      · intro m
        rw [RingHom.comp_apply, e2]
        exact hcS m

end P2mWs2K5b

set_option maxHeartbeats 3200000 in
open P2mWs2K5b in
theorem solution
    {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ Γ' : Subgroup G)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (D : FormalQuotientDatum 𝒪 π K₀ Onr Fr vdet r σ Γ Γ' g₁)

    (sn : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
    (hsn : ∀ n : ℕ, sn n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))
    (tn : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1 + 1)})))
    (htn : ∀ n : ℕ, tn n = Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 Onr π) (Nat.le_succ (n + 1)))))))
    (htsn : ∀ n : ℕ, tn n ≫ sn (n + 1) = sn n)

    (jn : ∀ n : ℕ, Limits.pullback f (sn n) ⟶ Limits.pullback f (sn (n + 1)))
    (hjn₁ : ∀ n : ℕ, jn n ≫ Limits.pullback.fst f (sn (n + 1)) = Limits.pullback.fst f (sn n))
    (hjn₂ : ∀ n : ℕ, jn n ≫ Limits.pullback.snd f (sn (n + 1)) = Limits.pullback.snd f (sn n) ≫ tn n)

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (v : ∀ n : ℕ, D.Y n ⟶ Limits.pullback f (sR n))
    (hv_over : ∀ n : ℕ, v n ≫ Limits.pullback.snd f (sR n) = D.yb n)
    (hv_sq : ∀ n : ℕ, IsPullback (D.yt n) (v n) (v (n + 1)) (xn n))
    (hv_q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      D.q n B hB x ≫ v n ≫ Limits.pullback.fst f (sR n) = (Θ B ⟨n + 1, hB⟩ x).1)
    (hv_iso : ∀ n : ℕ, IsIso (v n)) :
    ∃ (U : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (Limits.pullback f (sn n)).Opens)
      (c : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        ↑((Limits.pullback f (sn n)).presheaf.obj (Opposite.op (U h n))) →+* ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))
      (κ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Limits.pullback f (sn n)),

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (κ h n) ⁻¹ᵁ (U h n) = ⊤ ∧
        ∀ (hle : (⊤ : (Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).Opens) ≤ (κ h n) ⁻¹ᵁ (U h n))
          (s : ↑((Limits.pullback f (sn n)).presheaf.obj (Opposite.op (U h n)))),
          c h n s = (Scheme.ΓSpecIso (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).hom.hom
            ((Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).presheaf.map (homOfLE hle).op (((κ h n).app (U h n)).hom s))) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ) (y : Onr),
        c h n ((Limits.pullback f (sn n)).presheaf.map (homOfLE le_top).op
          ((Limits.pullback.snd f (sn n)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))).inv.hom
            (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) y)))) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) y)) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
        U h n = (jn n) ⁻¹ᵁ (U h (n + 1)) ∧
        ∀ (hle : U h n ≤ (jn n) ⁻¹ᵁ (U h (n + 1))) (s : ↑((Limits.pullback f (sn (n + 1))).presheaf.obj (Opposite.op (U h (n + 1))))),
          c h n ((Limits.pullback f (sn n)).presheaf.map (homOfLE hle).op (((jn n).app (U h (n + 1))).hom s)) =
          Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (n + 1)))) (c h (n + 1) s)) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          (Θ B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)).1 =
            Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ h n ≫ Limits.pullback.fst f (sn n)) ∧

      (∀ n : ℕ, ⨆ h : Matrix.GeneralLinearGroup (Fin 2) K₀, U h n = ⊤) ∧

      (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀),
        (∀ (s s' : ∀ m : ℕ, ↑((Limits.pullback f (sn m)).presheaf.obj (Opposite.op (U h m)))),
          (∀ (m : ℕ) (hle : U h m ≤ (jn m) ⁻¹ᵁ (U h (m + 1))),
              (Limits.pullback f (sn m)).presheaf.map (homOfLE hle).op (((jn m).app (U h (m + 1))).hom (s (m + 1))) = s m) →
          (∀ (m : ℕ) (hle : U h m ≤ (jn m) ⁻¹ᵁ (U h (m + 1))),
              (Limits.pullback f (sn m)).presheaf.map (homOfLE hle).op (((jn m).app (U h (m + 1))).hom (s' (m + 1))) = s' m) →
          (∀ m : ℕ, c h m (s m) = c h m (s' m)) → s = s') ∧
        ∀ fam : ∀ m : ℕ, ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}), (∀ m : ℕ, Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (m + 1)))) (fam (m + 1)) = fam m) →
          ((∃ s : ∀ m : ℕ, ↑((Limits.pullback f (sn m)).presheaf.obj (Opposite.op (U h m))),
              (∀ (m : ℕ) (hle : U h m ≤ (jn m) ⁻¹ᵁ (U h (m + 1))),
              (Limits.pullback f (sn m)).presheaf.map (homOfLE hle).op (((jn m).app (U h (m + 1))).hom (s (m + 1))) = s m) ∧
              ∀ m : ℕ, c h m (s m) = fam m) ↔
            ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B],
              IsNilpotent (algebraMap 𝒪 B π) →
              ∀ (xbar xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B) (d d' P P' : DeligneDatum (K := K₀) π B),
                (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                (d'.line (stdFullLattice K₀) =
              Submodule.span B {(xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d' P' →
                (∃ γ ∈ Γ', DeligneDatum.IsPullback (K := K₀) (π := π) B (σ γ)⁻¹ P P') →
                xbar (fam m) = xbar' (fam m))) := by
  classical

  have hmono : ∀ n : ℕ, Mono (sR n) := by
    intro n
    haveI : IsClosedImmersion (sR n) := by
      rw [hsR]; exact IsClosedImmersion.spec_of_surjective _ (fun b => Ideal.Quotient.mk_surjective b)
    infer_instance
  have hIJ : ∀ n : ℕ, Ideal.span {π ^ (n + 1)} ≤
      (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}).comap (algebraMap 𝒪 Onr) := by
    intro n
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  let a : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 Onr) (hIJ n)))
  have ha : ∀ n : ℕ, a n ≫ sR n = sn n := by
    intro n
    rw [hsR, hsn, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  obtain ⟨E, hE₁, hE₂, hEj⟩ : ∃ E : ∀ n : ℕ, D.Ynr n ≅ pullback f (sn n),
      (∀ n : ℕ, (E n).hom ≫ pullback.fst f (sn n) = D.p₁ n ≫ v n ≫ pullback.fst f (sR n)) ∧
      (∀ n : ℕ, (E n).hom ≫ pullback.snd f (sn n) = D.p₂ n) ∧
      (∀ n : ℕ, D.jnr n ≫ (E (n + 1)).hom = (E n).hom ≫ jn n) := by

    have hpa : ∀ n : ℕ, D.p₂ n ≫ a n = D.p₁ n ≫ D.yb n := by
      intro n
      haveI := hmono n
      rw [← cancel_mono (sR n), Category.assoc, ha, hsn, Category.assoc, hsR]
      exact (D.isPullback_nr n).w.symm
    have hw : ∀ n : ℕ, (D.p₁ n ≫ v n ≫ pullback.fst f (sR n)) ≫ f = D.p₂ n ≫ sn n := by
      intro n
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (v n), hv_over, ← ha,
        ← Category.assoc (D.p₂ n) (a n) (sR n), hpa, Category.assoc]
    have hw' : ∀ n : ℕ, pullback.fst f (sn n) ≫ f = (pullback.snd f (sn n) ≫ a n) ≫ sR n := by
      intro n; rw [Category.assoc, ha, pullback.condition]
    let τ : ∀ n : ℕ, pullback f (sn n) ⟶ pullback f (sR n) :=
      fun n => pullback.lift (pullback.fst f (sn n)) (pullback.snd f (sn n) ≫ a n) (hw' n)
    have hwi : ∀ n : ℕ, (τ n ≫ inv (v n)) ≫ D.yb n ≫
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        pullback.snd f (sn n) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))) := by
      intro n
      haveI := hv_iso n
      rw [← hsR, ← hv_over n]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [pullback.lift_snd_assoc, Category.assoc, ha, ← hsn]
    let hom : ∀ n : ℕ, D.Ynr n ⟶ pullback f (sn n) :=
      fun n => pullback.lift (D.p₁ n ≫ v n ≫ pullback.fst f (sR n)) (D.p₂ n) (hw n)
    let inv' : ∀ n : ℕ, pullback f (sn n) ⟶ D.Ynr n :=
      fun n => (D.isPullback_nr n).lift (τ n ≫ inv (v n)) (pullback.snd f (sn n)) (hwi n)
    have hτ : ∀ n : ℕ, hom n ≫ τ n = D.p₁ n ≫ v n := by
      intro n
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hpa, Category.assoc, hv_over]
    refine ⟨fun n => ⟨hom n, inv' n, ?_, ?_⟩, fun n => pullback.lift_fst _ _ _, fun n => pullback.lift_snd _ _ _, ?_⟩
    · haveI := hv_iso n
      apply (D.isPullback_nr n).hom_ext
      · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, hτ, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id, Category.id_comp]
      · rw [Category.assoc, IsPullback.lift_snd, pullback.lift_snd, Category.id_comp]
    · haveI := hv_iso n
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, IsPullback.lift_fst, Category.assoc,
          IsIso.inv_hom_id_assoc, pullback.lift_fst, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, IsPullback.lift_snd, Category.id_comp]
    · intro n
      apply pullback.hom_ext
      · show (D.jnr n ≫ hom (n + 1)) ≫ _ = (hom n ≫ jn n) ≫ _
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, D.jnr_p₁, Category.assoc,
          ← Category.assoc (D.yt n) (v (n + 1)), (hv_sq n).w, Category.assoc, hxn₁, Category.assoc, hjn₁, pullback.lift_fst]
      · show (D.jnr n ≫ hom (n + 1)) ≫ _ = (hom n ≫ jn n) ≫ _
        rw [Category.assoc, pullback.lift_snd, D.jnr_p₂, Category.assoc, hjn₂, ← Category.assoc, pullback.lift_snd, htn]

  have hEj' : ∀ n : ℕ, (E n).inv ≫ D.jnr n = jn n ≫ (E (n + 1)).inv := by
    intro n
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hEj, Category.assoc, Iso.hom_inv_id, Category.comp_id]

  have hUle : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), D.U h n ≤ (E n).hom ⁻¹ᵁ ((E n).inv ⁻¹ᵁ (D.U h n)) := by
    intro h n
    rw [← Scheme.Hom.comp_preimage, Iso.hom_inv_id]
    exact le_rfl
  have hUle' : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (E n).inv ⁻¹ᵁ (D.U h n) ≤ (E n).inv ⁻¹ᵁ (D.U h n) :=
    fun h n => le_rfl

  have hfb : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      (E n).inv.appLE (D.U h n) ((E n).inv ⁻¹ᵁ (D.U h n)) (hUle' h n) ≫
        (E n).hom.appLE ((E n).inv ⁻¹ᵁ (D.U h n)) (D.U h n) (hUle h n) = 𝟙 _ := by
    intro h n
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (E n).hom_inv_id (D.U h n) (D.U h n) _ le_rfl, id_appLE]
  have hbf : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      (E n).hom.appLE ((E n).inv ⁻¹ᵁ (D.U h n)) (D.U h n) (hUle h n) ≫
        (E n).inv.appLE (D.U h n) ((E n).inv ⁻¹ᵁ (D.U h n)) (hUle' h n) = 𝟙 _ := by
    intro h n
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (E n).inv_hom_id ((E n).inv ⁻¹ᵁ (D.U h n)) ((E n).inv ⁻¹ᵁ (D.U h n)) _ le_rfl,
      id_appLE]
  refine ⟨fun h n => (E n).inv ⁻¹ᵁ (D.U h n),
    fun h n => (D.c h n).comp ((E n).hom.appLE ((E n).inv ⁻¹ᵁ (D.U h n)) (D.U h n) (hUle h n)).hom,
    fun h n => D.κ h n ≫ (E n).hom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h n
    have hpre : (D.κ h n ≫ (E n).hom) ⁻¹ᵁ ((E n).inv ⁻¹ᵁ (D.U h n)) = D.κ h n ⁻¹ᵁ (D.U h n) := by
      rw [Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage (E n).hom, Iso.hom_inv_id]; rfl
    refine ⟨by rw [hpre]; exact (D.κ_preimage h n).1, fun hle s => ?_⟩
    have hle₀ : (⊤ : (Spec _).Opens) ≤ D.κ h n ⁻¹ᵁ (D.U h n) := by rw [← hpre]; exact hle
    refine ((D.κ_preimage h n).2 hle₀ (((E n).hom.appLE ((E n).inv ⁻¹ᵁ (D.U h n)) (D.U h n) (hUle h n)).hom s)).trans ?_
    have key : (E n).hom.appLE ((E n).inv ⁻¹ᵁ (D.U h n)) (D.U h n) (hUle h n) ≫ (D.κ h n).app (D.U h n) ≫
          (Spec _).presheaf.map (homOfLE hle₀).op =
        (D.κ h n ≫ (E n).hom).app ((E n).inv ⁻¹ᵁ (D.U h n)) ≫ (Spec _).presheaf.map (homOfLE hle).op := by
      show _ ≫ (D.κ h n).appLE (D.U h n) ⊤ hle₀ = (D.κ h n ≫ (E n).hom).appLE ((E n).inv ⁻¹ᵁ (D.U h n)) ⊤ hle
      rw [Scheme.Hom.appLE_comp_appLE]
    have key' := congrArg (fun φ => φ.hom s) key
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at key'
    exact congrArg _ key'
  ·
    intro h n y
    have hc := D.c_const h n y
    rw [← hE₂ n, Scheme.Hom.comp_appTop] at hc
    refine Eq.trans ?_ hc
    have k : (pullback f (sn n)).presheaf.map (homOfLE (le_top : (E n).inv ⁻¹ᵁ (D.U h n) ≤ ⊤)).op ≫
        (E n).hom.appLE ((E n).inv ⁻¹ᵁ (D.U h n)) (D.U h n) (hUle h n) =
        (E n).hom.appTop ≫ (D.Ynr n).presheaf.map (homOfLE (le_top : D.U h n ≤ ⊤)).op := by
      rw [Scheme.Hom.map_appLE]; rfl
    have k' := congrArg (fun φ => φ.hom (((pullback.snd f (sn n)).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))).inv.hom
        (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) y)))) k
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at k'
    exact congrArg (D.c h n) k'
  ·
    intro h n
    exact transport_transitions (D.jnr n) (jn n) (E n) (E (n + 1)) (hEj n) (D.U h n) (D.U h (n + 1))
      (hUle h n) (hUle h (n + 1)) (D.c h n) (D.c h (n + 1)) _ (D.U_jnr h n)
  ·
    intro h n B _ _ _ _ hB xbar d P hd hP
    have hJ : algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
        ((algebraMap 𝒪 Onr π) ^ (n + 1)) = 0 := by
      rw [← Ideal.Quotient.mk_comp_algebraMap, RingHom.comp_apply, map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hBn : (algebraMap 𝒪 B π) ^ (n + 1) = 0 := by
      rw [IsScalarTower.algebraMap_apply 𝒪 Onr B π, ← map_pow, ← AlgHom.commutes xbar, hJ, map_zero]
    have hq := D.κ_p₁ h n B hBn xbar d P hd hP
    have hvq := hv_q n B hBn ((IsScalarTower.toAlgHom 𝒪 Onr B), P)
    rw [show Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ (D.κ h n ≫ (E n).hom) ≫ pullback.fst f (sn n) =
        (Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ D.κ h n ≫ D.p₁ n) ≫ v n ≫ pullback.fst f (sR n) by
      simp only [Category.assoc, hE₁], hq, hvq]
  ·
    intro n
    exact (E n).inv.iSup_preimage_eq_top (D.cover n)
  ·
    intro h
    exact transport_functions D.Ynr (fun m => pullback f (sn m)) D.jnr jn E hEj (D.U h)
      (fun m => (D.U_jnr h m).1) (hUle h) (hUle' h) _ (D.c h) (D.functions h)

end S_CerednikDrinfeld_exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso
end P2MW
export P2MW.S_CerednikDrinfeld_exists_opens_chartMorphism_of_formalQuotientDatum_of_isIso (solution)
