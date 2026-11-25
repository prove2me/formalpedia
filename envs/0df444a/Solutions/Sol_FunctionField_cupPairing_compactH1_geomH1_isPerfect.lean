-- Prove2me | solution 1 for FunctionField.cupPairing_compactH1_geomH1_isPerfect
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T14:38:56.394868+00:00
-- url     : https://prove2.me/submissions/d5a30b85-a6a2-4f4e-a0e9-7c82e0f2e24e

import Mathlib
import Definitions.Def_RPLib_F2_065
import Definitions.Def_RPLib_F2_031
import Definitions.Def_RPLib_F2_067

set_option autoImplicit false

namespace RamanujanPetersson.SW05Aux

/-- The statement of the Proved theorem
`FunctionField.geomPic_affine_divisible_and_geomPic0_divisible` (7fe70d9b), same proof. -/
theorem picDiv_explicit
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (l : ℕ) [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (CL : ℕ → IntermediateField F (AlgebraicClosure F))
    (hCL : ∀ m, CL m = IntermediateField.adjoin F
      (((Polynomial.X : Polynomial F) ^ (p ^ m) - Polynomial.X).rootSet (AlgebraicClosure F)))
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1) :
    (∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) M)]
        [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) M) M]
        (D : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M) → ℤ),
        (Function.support D).Finite →
        ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
          ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))]
            [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
              ↥(M ⊔ CL m)]
            (w : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
              ↥(M ⊔ CL m)))
            (v : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M)),
            (∀ x : integralClosure (FunctionField.ringOfIntegers Fq F) M, x ∈ v.asIdeal ↔
              ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                  AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
            (l : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a)) ∧
    (∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)]
        [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) M]
        (r : ℕ),
        (∀ w : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M),
          Nat.card (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M ⧸
            w.asIdeal) = r) →
        ∀ D : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) → ℤ,
          (Function.support D).Finite → ∑ᶠ w, D w = 0 →
          ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
            (∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (y : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))),
              ((l ^ n : ℕ) : ℤ) ∣ WithZero.log (y.valuation ↥(M ⊔ CL m) a)) ∧
            ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (w : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m)))
              (v : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)),
              (∀ x : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M,
                x ∈ v.asIdeal ↔ ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                    AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
              ((l ^ n : ℕ) : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a)) := by
  classical
  -- `l ∤ q`
  have hlq : ¬ l ∣ Fintype.card Fq := by
    obtain ⟨p', hpc⟩ := CharP.exists Fq
    obtain ⟨e, hp', hq⟩ := FiniteField.card Fq p'
    intro hdvd
    rw [hq] at hdvd
    have hlp : l = (p' : ℕ) :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hp').1 ((Fact.out : l.Prime).dvd_of_dvd_pow hdvd)
    apply hl
    rw [hlp, ← map_natCast (algebraMap Fq F), CharP.cast_eq_zero, map_zero]
  -- `K_U = maxUnram`
  have hset : unramSet (FunctionField.ringOfIntegers Fq F) F =
      {L : IntermediateField F (AlgebraicClosure F) | FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (CDBridge.unram_iff _ F L))
  have hKU' : KU = maxUnram (FunctionField.ringOfIntegers Fq F) F := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have hCL' : CL = Kummer.constLevel F p := funext hCL
  subst hCL'
  have hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l := Lefschetz.picDivU Fq F l hlq
  have hPic : Residue.PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n) :=
    Lefschetz.picDivX Fq F l hlq n
  refine ⟨?_, ?_⟩
  · intro M hM hMU i1 i2 D hD
    obtain ⟨m, hm, a, ha, H⟩ := @hPicU M hM hMU i1 i2 D hD
    refine ⟨m, hm, a, ha, ?_⟩
    intro i3 i4 w v hv
    have hveq :=
      IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x =>
        (hv x).trans (@CDBridge.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w x).symm)
    rw [hveq]
    exact @H i3 i4 w
  · intro M hM hMU i1 i2 r hr D hD hsum
    obtain ⟨m, hm, a, ha, H1, H2⟩ := @hPic M hM hMU i1 i2 r hr D hD hsum
    refine ⟨m, hm, a, ha, fun {i5 i6} y => @H1 i5 i6 y, ?_⟩
    intro i3 i4 w v hv
    have hveq :=
      IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x =>
        (hv x).trans (@CDBridge.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w x).symm)
    rw [hveq]
    exact @H2 i3 i4 w

end RamanujanPetersson.SW05Aux

open RamanujanPetersson in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hk : algebraicClosure Fq F = ⊥)
    (l : ℕ) [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (CL : ℕ → IntermediateField F (AlgebraicClosure F))
    (hCL : ∀ m, CL m = IntermediateField.adjoin F
      (((Polynomial.X : Polynomial F) ^ (p ^ m) - Polynomial.X).rootSet (AlgebraicClosure F)))
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
    (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (P : S → Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU))
    (hP : ∀ s, (P s).IsPrime ∧ P s ≠ ⊥)
    (hcover : ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
      Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
        ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU))
    (hdisj : ∀ s s', ∀ g ∈ Γ,
      (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s')
    (I : S → Subgroup (KU ≃ₐ[F] KU))
    (hI : ∀ s (g : KU ≃ₐ[F] KU), g ∈ I s ↔
      ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, ∃ c ∈ P s, (c : KU) = g (b : KU) - b)
    (Λ : Type) [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (KU ≃ₐ[F] KU) Λ) (hσ : IsOpen (σ.ker : Set (KU ≃ₐ[F] KU)))
    (htriv : ∀ g ∈ Γ, ∀ x : Λ, σ g x = x) :
    ∃ t : S → Γ, (∀ s, (t s : KU ≃ₐ[F] KU) ∈ I s) ∧
      (∀ c d : Γ → Λ, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + c h) →
        (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
        ∃ u : Γ → Λ, IsLocallyConstant u ∧ ∀ g h, c g * d h = u h - u (g * h) + u g) ∧
      ∃ pair : (Γ → Λ) × (S → Λ) → (Γ → Λ) → Λ,
        (∀ (x : (Γ → Λ) × (S → Λ)) (d u : Γ → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
          (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
          (IsLocallyConstant u ∧ ∀ g h, x.1 g * d h = u h - u (g * h) + u g) →
          pair x d = ∑ s, (x.2 s * d (t s) - u (t s))) ∧
        (∀ x : (Γ → Λ) × (S → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
          (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → pair x d = 0) →
          x.1 = 0 ∧ ∃ a : Λ, ∀ s, x.2 s = a) ∧
        (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
          (∀ x : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → pair x d = 0) →
          d = 0) ∧
        (∀ f : (Γ → Λ) → Λ,
          (∀ d d' : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
            (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) → f (d + d') = f d + f d') →
          (∀ (a : Λ) (d : Γ → Λ), (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
            f (a • d) = a * f d) →
          ∃ x : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) ∧
            ∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → pair x d = f d) ∧
        (∀ f : (Γ → Λ) × (S → Λ) → Λ,
          (∀ x y : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
            (IsLocallyConstant y.1 ∧ (∀ g h, y.1 (g * h) = y.1 g + y.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → y.1 g = 0) → f (x + y) = f x + f y) →
          (∀ (a : Λ) (x : (Γ → Λ) × (S → Λ)),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → f (a • x) = a * f x) →
          (∀ a : Λ, f (0, fun _ => a) = 0) →
          ∃ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) ∧
            ∀ x : (Γ → Λ) × (S → Λ),
              (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → pair x d = f x) ∧
        ∀ φ : KU ≃ₐ[F] KU, (∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) →
            φ x = x ^ Fintype.card Fq) →
          ∃ τ : S → S, ∃ η : S → Γ,
            (∀ s (b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU), (∃ c ∈ P s, (b : KU) = φ (c : KU)) ↔
              ∃ c ∈ P (τ s), (b : KU) = (η s : KU ≃ₐ[F] KU) (c : KU)) ∧
            ∀ (x : (Γ → Λ) × (S → Λ)) (d c' d' : Γ → Λ),
              (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
              (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
              (∀ g g' : Γ, (g' : KU ≃ₐ[F] KU) = φ * g * φ⁻¹ → c' g = x.1 g' ∧ d' g = σ φ⁻¹ (d g')) →
              (IsLocallyConstant c' ∧ (∀ g h, c' (g * h) = c' g + c' h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → c' g = 0) ∧
              (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) ∧
              pair (c', fun s => x.2 (τ s) - x.1 (η s)) d' =
                ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) * pair x d := by
  obtain ⟨p', hpc⟩ := CharP.exists Fq
  obtain ⟨e, hp', hq'⟩ := FiniteField.card Fq p'
  have hpp : p' = p := by
    have : CharP F p' := charP_of_injective_algebraMap (algebraMap Fq F).injective p'
    exact CharP.eq F this ‹CharP F p›
  have hq : Fintype.card Fq = p ^ (e : ℕ) := hpp ▸ hq'
  have H := SW05Aux.picDiv_explicit Fq F p l hl n CL hCL KU hKU
  exact CDSol.bridge (@RamanujanPetersson.CupDuality.constDuality_S3_perfect) Fq F p (e : ℕ) hq e.pos hk l hl n CL hCL
    KU hKU H.1 H.2 Γ hΓ S P hP hcover hdisj I hI Λ hΛ σ hσ htriv
