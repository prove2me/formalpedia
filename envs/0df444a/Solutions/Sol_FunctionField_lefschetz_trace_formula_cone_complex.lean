-- Prove2me | solution 1 for FunctionField.lefschetz_trace_formula_cone_complex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-19T23:53:17.610894+00:00
-- url     : https://prove2.me/submissions/9ad5c802-c08b-4ba9-9503-c75cb0832618

import Mathlib
import Definitions.Def_RPLib_F2_070
import Definitions.Def_RPLib_F2_045

set_option autoImplicit false

theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p e : ℕ) [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[F] KU))
    (hΓ : ∀ g : KU ≃ₐ[F] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (φ : KU ≃ₐ[F] KU)
    (hφ : ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → φ x = x ^ Fintype.card Fq)
    (Mf : IntermediateField F (AlgebraicClosure F))
    (hMf : FiniteDimensional F Mf ∧ IsGalois F Mf ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) Mf), P.IsPrime →
        ∀ g : Mf ≃ₐ[F] Mf,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) Mf, ∃ c ∈ P, (c : Mf) = g b - b) →
            g = 1)
    (hMfU : Mf ≤ KU)
    (Gf : Type) [Group Gf] [Fintype Gf] (π : (KU ≃ₐ[F] KU) →* Gf)
    (hπ : ∀ σ : KU ≃ₐ[F] KU, π σ = 1 ↔ ∀ x : KU, (x : AlgebraicClosure F) ∈ Mf → σ x = x)
    (hπo : IsOpen (π.ker : Set (KU ≃ₐ[F] KU)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    (Z1 : Submodule (ZMod (l ^ n)) (Γ → M))
    (hZ1 : ∀ c : Γ → M, c ∈ Z1 ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + τ (π g) (c h))
    (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : 0 < r) (hmr : m * Fintype.card Gf ∣ r)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (Cr : Subfield KU) (hCr : ∀ x : KU, x ∈ Cr ↔ x ^ (Fintype.card Fq ^ r) = x) (ιS : Cr →+* Ω)
    (S : Finset (FunctionField.ringOfIntegers Fq F →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (∀ (c : Fq) (x : Cr), (x : KU) = algebraMap F KU (algebraMap Fq F c) →
        u (algebraMap Fq (FunctionField.ringOfIntegers Fq F) c) = ιS x) ∧ Fr.comp u = u)
    (Fu : (FunctionField.ringOfIntegers Fq F →+* Ω) → (KU ≃ₐ[F] KU))
    (hFu : ∀ u ∈ S, ∃ w : integralClosure (FunctionField.ringOfIntegers Fq F) KU →+* Ω,
      (∀ a : FunctionField.ringOfIntegers Fq F, w (algebraMap _ _ a) = u a) ∧
      (∀ b b' : integralClosure (FunctionField.ringOfIntegers Fq F) KU,
        (b' : KU) = Fu u (b : KU) → w b' = Fr (w b)) ∧
      ∀ (x : Cr) (b : integralClosure (FunctionField.ringOfIntegers Fq F) KU), (b : KU) = x → w b = ιS x) :
    ∃ (B : Type) (P : B → Ideal (integralClosure
        (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU)),
      Finite B ∧ (∀ s, (P s).IsPrime ∧ P s ≠ ⊥) ∧
      (∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
        Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
          ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
            b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) ∧
      (∀ s s', ∀ g ∈ Γ,
        (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
          b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s') ∧
      ∃ (t : B → B) (h : B → Γ),
        (∀ s (b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
          (∃ c ∈ P s, (b : KU) = φ (c : KU)) ↔
            ∃ c ∈ P (t s), (b : KU) = (h s : KU ≃ₐ[F] KU) (c : KU)) ∧
        ∀ I : B → Subgroup (KU ≃ₐ[F] KU),
          (∀ s (g : KU ≃ₐ[F] KU), g ∈ I s ↔
            ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
              ∃ c ∈ P s, (c : KU) = g (b : KU) - b) →
        ∀ Z2 : (s : B) → Submodule (ZMod (l ^ n)) (↥(Γ ⊓ I s) → M),
          (∀ s (c : ↥(Γ ⊓ I s) → M), c ∈ Z2 s ↔
            IsLocallyConstant c ∧ ∀ g h : ↥(Γ ⊓ I s), c (g * h) = c g + τ (π g) (c h)) →
        ∃ (F1 : (↥Z1 × (B → M)) →ₗ[ZMod (l ^ n)] (↥Z1 × (B → M)))
          (F2 : ((s : B) → ↥(Z2 s)) →ₗ[ZMod (l ^ n)] ((s : B) → ↥(Z2 s))),
          (∀ (c : ↥Z1) (y : B → M) (g g' : Γ), (g' : KU ≃ₐ[F] KU) = φ * g * φ⁻¹ →
            ((F1 (c, y)).1 : Γ → M) g = τ (π φ⁻¹) ((c : Γ → M) g')) ∧
          (∀ (c : ↥Z1) (y : B → M) (s : B),
            (F1 (c, y)).2 s = τ (π φ⁻¹) (τ (π (h s)) (y (t s)) - (c : Γ → M) (h s))) ∧
          (∀ (x : (s : B) → ↥(Z2 s)) (s : B) (g : ↥(Γ ⊓ I s)) (g' : ↥(Γ ⊓ I (t s))),
            (g' : KU ≃ₐ[F] KU) = (h s : KU ≃ₐ[F] KU)⁻¹ * φ * g * φ⁻¹ * h s →
            ((F2 x s : ↥(Z2 s)) : ↥(Γ ⊓ I s) → M) g =
              τ (π (φ⁻¹ * h s)) (((x (t s) : ↥(Z2 (t s))) : ↥(Γ ⊓ I (t s)) → M) g')) ∧
          LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
              LinearMap.trace (ZMod (l ^ n)) (↥Z1 × (B → M)) (F1 ^ m) +
              LinearMap.trace (ZMod (l ^ n)) ((s : B) → ↥(Z2 s)) (F2 ^ m) =
            ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹) := by
  exact LefschetzSol.bridge (@RamanujanPetersson.Lefschetz.lefschetz_main) Fq F p e hq he l n hn hlq KU hKU Γ hΓ φ hφ Mf hMf hMfU Gf π hπ hπo M τ Z1 hZ1 m hm r hr hmr Ω Fr hFr Cr hCr ιS S hS Fu hFu
