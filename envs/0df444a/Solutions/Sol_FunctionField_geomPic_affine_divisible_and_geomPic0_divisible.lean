-- Prove2me | solution 1 for FunctionField.geomPic_affine_divisible_and_geomPic0_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T14:07:59.364801+00:00
-- url     : https://prove2.me/submissions/1bf098f4-5863-4f45-abf7-3dc29d5defb7

import Mathlib
import Definitions.Def_RPLib_F2_067

set_option autoImplicit false

namespace RamanujanPetersson.SW05Aux

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

theorem under_iff {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K]
    [IsFractionRing A K] {M L : IntermediateField K (AlgebraicClosure K)} (h : M ≤ L)
    [IsDedekindDomain (integralClosure A M)] [IsDedekindDomain (integralClosure A L)]
    (w : IsDedekindDomain.HeightOneSpectrum (integralClosure A L)) (x : integralClosure A M) :
    x ∈ (CdOne.underI A h w).asIdeal ↔
      ∃ y ∈ w.asIdeal, ((y : L) : AlgebraicClosure K) = ((x : M) : AlgebraicClosure K) := by
  show x ∈ w.asIdeal.comap (incl A K h) ↔ _
  rw [Ideal.mem_comap]
  constructor
  · intro hx
    exact ⟨_, hx, incl_val A K h x⟩
  · rintro ⟨y, hy, he⟩
    have : y = incl A K h x := Subtype.ext (Subtype.ext (he.trans (incl_val A K h x).symm))
    rwa [← this]

end RamanujanPetersson.SW05Aux

open RamanujanPetersson in
theorem solution
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
    exact and_congr Iff.rfl (and_congr Iff.rfl (SW05Aux.unram_iff _ F L))
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
        (hv x).trans (@SW05Aux.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w x).symm)
    rw [hveq]
    exact @H i3 i4 w
  · intro M hM hMU i1 i2 r hr D hD hsum
    obtain ⟨m, hm, a, ha, H1, H2⟩ := @hPic M hM hMU i1 i2 r hr D hD hsum
    refine ⟨m, hm, a, ha, fun {i5 i6} y => @H1 i5 i6 y, ?_⟩
    intro i3 i4 w v hv
    have hveq :=
      IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x =>
        (hv x).trans (@SW05Aux.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w x).symm)
    rw [hveq]
    exact @H2 i3 i4 w
