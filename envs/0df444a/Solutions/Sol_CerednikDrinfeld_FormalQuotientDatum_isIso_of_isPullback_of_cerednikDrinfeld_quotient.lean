-- Prove2me | solution 1 for CerednikDrinfeld.FormalQuotientDatum.isIso_of_isPullback_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2d3a993c-87d4-5d74-8c73-4eb926361248

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalQuotientDatum_isIso_of_isPullback_of_cerednikDrinfeld_quotient

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ Γ' : Subgroup G)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (D : FormalQuotientDatum 𝒪 π K₀ Onr Fr vdet r σ Γ Γ' g₁)

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

    (Yf : Scheme.{0}) (Gf : Yf ⟶ 𝒳) (φ : ∀ n : ℕ, D.Y n ⟶ Yf)
    (hφ : ∀ n : ℕ, IsPullback (φ n) (v n) Gf (Limits.pullback.fst f (sR n)))
    (hφt : ∀ n : ℕ, D.yt n ≫ φ (n + 1) = φ n) :
    ∀ n : ℕ, IsIso (v n) := by
  classical

  have hpow_mono : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (n m : ℕ), n ≤ m →
      (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (algebraMap 𝒪 B π) ^ (m + 1) = 0 :=
    fun B _ _ n m h hn => pow_eq_zero_of_le (by omega) hn
  have hpow : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)),
      (algebraMap 𝒪 B π) ^ (hB.choose + 1) = 0 := by
    intro B _ _ hB
    rw [pow_succ, hB.choose_spec, zero_mul]

  have hstep : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (n : ℕ) (hn : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (hn1 : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      D.q (n + 1) B hn1 x ≫ φ (n + 1) = D.q n B hn x ≫ φ n := by
    intro B _ _ n hn hn1 x
    rw [D.q_yt n B hn hn1 x, Category.assoc, hφt]
  have hqφ_le : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (n m : ℕ), n ≤ m →
      ∀ (hn : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hm : (algebraMap 𝒪 B π) ^ (m + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      D.q m B hm x ≫ φ m = D.q n B hn x ≫ φ n := by
    intro B _ _ n m hle
    induction hle with
    | refl => intro hn hm x; rfl
    | step hle ih =>
      intro hn hm x
      rw [hstep B _ (hpow_mono B n _ hle hn) hm x]
      exact ih hn _ x
  have hqφ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (n m : ℕ)
      (hn : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hm : (algebraMap 𝒪 B π) ^ (m + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      D.q n B hn x ≫ φ n = D.q m B hm x ≫ φ m := by
    intro B _ _ n m hn hm x
    rcases le_total n m with h | h
    · exact (hqφ_le B n m h hn hm x).symm
    · exact hqφ_le B m n h hm hn x

  have hqφf : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      (D.q n B hB x ≫ φ n) ≫ (Gf ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)) := by
    intro n B _ _ hB x
    rw [Category.assoc, ← Category.assoc (φ n), (hφ n).w, Category.assoc, Limits.pullback.condition,
      ← Category.assoc (v n), hv_over, hsR]
    exact D.q_over n B hB x

  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints (Gf ≫ f)).obj B,
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        (ρ' B hB x).1 = D.q hB.choose B (hpow B hB) x ≫ φ hB.choose :=
    ⟨fun B _ _ hB x => ⟨D.q hB.choose B (hpow B hB) x ≫ φ hB.choose, hqφf _ B (hpow B hB) x⟩,
      fun B _ _ hB x => rfl⟩
  have hρ'n : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hn : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      (ρ' B hB x).1 = D.q n B hn x ≫ φ n := by
    intro n B _ _ hn hB x
    rw [hρ' B hB x, hqφ B _ n (hpow B hB) hn x]
  have hρ'nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (g : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map g x) = (Scheme.nilpPoints (Gf ≫ f)).map g (ρ' B hB x) := by
    intro B _ _ B' _ _ hB hB' g x
    apply Subtype.ext
    have hB'n : (algebraMap 𝒪 B' π) ^ (hB.choose + 1) = 0 := by
      rw [← g.commutes, ← map_pow, hpow B hB, map_zero]
    rw [Scheme.nilpPoints_map_val, hρ'n hB.choose B' hB'n hB' _, hρ' B hB x,
      D.q_natural hB.choose B B' (hpow B hB) hB'n g x, Category.assoc]
  have hρ'inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B, OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x := by
    intro B _ _ hB γ hγ x x' htw
    apply Subtype.ext
    rw [hρ' B hB x, hρ' B hB x', D.q_inv hB.choose B (hpow B hB) γ hγ x x' htw]
  obtain ⟨u, hu_nat, hu_Θ, -⟩ := hΘuniv Yf (Gf ≫ f) ρ' hρ'nat hρ'inv

  have hGu : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (y : (Scheme.nilpPoints f).obj B), (u B hB y).1 ≫ Gf = y.1 := by
    obtain ⟨u₀, -, -, huniq₀⟩ := hΘuniv 𝒳 f Θ hΘnat hΘinv
    have h1 := huniq₀
      (fun B _ _ hB y => ⟨(u B hB y).1 ≫ Gf, by rw [Category.assoc, (u B hB y).2]⟩)
      (fun B _ _ B' _ _ hB hB' g y => by
        apply Subtype.ext
        show (u B' hB' ((Scheme.nilpPoints f).map g y)).1 ≫ Gf =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫ ((u B hB y).1 ≫ Gf)
        rw [hu_nat B B' hB hB' g y, Scheme.nilpPoints_map_val, Category.assoc])
      (fun B _ _ hB x => by
        apply Subtype.ext
        show (u B hB (Θ B hB x)).1 ≫ Gf = (Θ B hB x).1
        rw [hu_Θ B hB x, hρ' B hB x, Category.assoc, (hφ _).w, ← Category.assoc]
        exact hv_q hB.choose B (hpow B hB) x)
    have h2 := huniq₀ (fun B _ _ hB y => y) (fun _ _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    intro B _ _ hB y
    exact congrArg Subtype.val ((h1 B hB y).trans (h2 B hB y).symm)

  have hb : ∀ n : ℕ, Limits.pullback.snd f (sR n) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Limits.pullback.fst f (sR n) ≫ f := fun n => by rw [← hsR n]; exact Limits.pullback.condition.symm
  have hsn := fun n : ℕ => AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural 𝒪 π 𝒳 f Yf (Gf ≫ f) u hu_nat
    (Limits.pullback f (sR n)) (Limits.pullback.fst f (sR n)) n (Limits.pullback.snd f (sR n)) (hb n)
  choose s hs using fun n : ℕ => (hsn n).exists
  have hsG : ∀ n : ℕ, s n ≫ Gf = Limits.pullback.fst f (sR n) := by
    intro n
    have hid := AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural 𝒪 π 𝒳 f 𝒳 f
      (fun B _ _ hB y => y) (fun _ _ _ _ _ _ _ _ _ _ => rfl)
      (Limits.pullback f (sR n)) (Limits.pullback.fst f (sR n)) n (Limits.pullback.snd f (sR n)) (hb n)
    refine hid.unique (y₁ := s n ≫ Gf) (y₂ := Limits.pullback.fst f (sR n)) ⟨?_, ?_⟩ ⟨rfl, fun B _ _ hB p hp => rfl⟩
    · rw [Category.assoc]; exact (hs n).1
    · intro B _ _ hB p hp
      rw [← Category.assoc, (hs n).2 B hB p hp]; exact hGu B hB _
  have hcomm : ∀ n : ℕ, s n ≫ Gf = 𝟙 _ ≫ Limits.pullback.fst f (sR n) := fun n => by
    rw [hsG, Category.id_comp]
  have hσφ : ∀ n : ℕ, (hφ n).lift (s n) (𝟙 _) (hcomm n) ≫ φ n = s n := fun n => (hφ n).lift_fst _ _ _
  have hσv : ∀ n : ℕ, (hφ n).lift (s n) (𝟙 _) (hcomm n) ≫ v n = 𝟙 _ := fun n => (hφ n).lift_snd _ _ _

  have hxs : ∀ n : ℕ, xn n ≫ s (n + 1) = s n := by
    intro n
    refine (hsn n).unique (y₁ := xn n ≫ s (n + 1)) (y₂ := s n) ⟨?_, ?_⟩ (hs n)
    · rw [Category.assoc, (hs (n + 1)).1, ← Category.assoc, hxn₁]
    · intro B _ _ hB p hp

      obtain ⟨p', hp'eq⟩ : ∃ p' : Spec (CommRingCat.of B) ⟶ Limits.pullback f (sR (n + 1)), p' = p ≫ xn n := ⟨_, rfl⟩
      have hp' : p' ≫ Limits.pullback.fst f (sR (n + 1)) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)) := by
        rw [hp'eq, Category.assoc, ← Category.assoc (xn n), hxn₁]; exact hp
      have h2 := (hs (n + 1)).2 B hB p' hp'
      have hpt : (⟨p' ≫ Limits.pullback.fst f (sR (n + 1)), hp'⟩ : (Scheme.nilpPoints f).obj B) =
          ⟨p ≫ Limits.pullback.fst f (sR n), hp⟩ :=
        Subtype.ext (show p' ≫ Limits.pullback.fst f (sR (n + 1)) = p ≫ Limits.pullback.fst f (sR n) by
          rw [hp'eq, Category.assoc, hxn₁])
      rw [hpt] at h2
      rw [← h2, hp'eq, Category.assoc]
  obtain ⟨uD, -, -, -, huD⟩ := D.univ Yf (Gf ≫ f) ρ' hρ'nat hρ'inv
  have hφsys : φ = uD := huD φ
    (fun n => by rw [← Category.assoc, (hφ n).w, Category.assoc, Limits.pullback.condition,
      ← Category.assoc, hv_over, hsR])
    hφt
    (fun n B _ _ hB x => (hρ'n n B hB ⟨n + 1, hB⟩ x).symm)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ m : ℕ, D.Y m ⟶ Yf, ∀ m, ψ m = v m ≫ s m := ⟨fun m => v m ≫ s m, fun m => rfl⟩
  have hψsys : ψ = uD := huD ψ
    (fun n => by
      rw [hψ, Category.assoc, (hs n).1, Limits.pullback.condition, ← Category.assoc, hv_over, hsR])
    (fun n => by
      rw [hψ, hψ, ← Category.assoc, (hv_sq n).w, Category.assoc, hxs])
    (fun n B _ _ hB x => by
      rw [hψ]
      obtain ⟨p', hp'eq⟩ : ∃ p' : Spec (CommRingCat.of B) ⟶ Limits.pullback f (sR n), p' = D.q n B hB x ≫ v n := ⟨_, rfl⟩
      have hp : p' ≫ Limits.pullback.fst f (sR n) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)) := by
        rw [hp'eq, Category.assoc, Limits.pullback.condition, ← Category.assoc (v n), hv_over, hsR]
        exact D.q_over n B hB x
      have h2 := (hs n).2 B ⟨n + 1, hB⟩ p' hp
      have hpt : (⟨p' ≫ Limits.pullback.fst f (sR n), hp⟩ : (Scheme.nilpPoints f).obj B) = Θ B ⟨n + 1, hB⟩ x :=
        Subtype.ext (show p' ≫ Limits.pullback.fst f (sR n) = (Θ B ⟨n + 1, hB⟩ x).1 by
          rw [hp'eq, Category.assoc]; exact hv_q n B hB x)
      rw [hpt, hu_Θ B ⟨n + 1, hB⟩ x] at h2
      rw [← Category.assoc, ← hp'eq, h2])
  have hvs : ∀ m : ℕ, v m ≫ s m = φ m := fun m => by
    rw [← hψ m, hψsys, ← hφsys]

  intro n
  refine ⟨⟨(hφ n).lift (s n) (𝟙 _) (hcomm n), ?_, hσv n⟩⟩
  apply (hφ n).hom_ext
  · rw [Category.assoc, hσφ, hvs, Category.id_comp]
  · rw [Category.assoc, hσv, Category.comp_id, Category.id_comp]

end S_CerednikDrinfeld_FormalQuotientDatum_isIso_of_isPullback_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_FormalQuotientDatum_isIso_of_isPullback_of_cerednikDrinfeld_quotient (solution)
