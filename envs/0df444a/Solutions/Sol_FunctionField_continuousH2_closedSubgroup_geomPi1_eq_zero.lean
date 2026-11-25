-- Prove2me | solution 1 for FunctionField.continuousH2_closedSubgroup_geomPi1_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:27:25.860941+00:00
-- url     : https://prove2.me/submissions/e39743ed-1dbb-4b1a-92aa-00e9b7350dc1

import Mathlib
import Definitions.Def_RPLib_F2_067

set_option autoImplicit false

namespace RamanujanPetersson.SW39Aux

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

end RamanujanPetersson.SW39Aux

open RamanujanPetersson in
open FunctionField in
theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (l : ℕ) [Fact l.Prime] (hl : ¬ l ∣ Fintype.card Fq)
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (Δ : Subgroup (KU ≃ₐ[F] KU)) (hΔc : IsClosed (Δ : Set (KU ≃ₐ[F] KU)))
    (hΔ : ∀ g ∈ Δ, ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (Λ : Type) [CommRing Λ] (M : Type) [AddCommGroup M] [Module Λ M] [Finite M]
    (ρ : Representation Λ (KU ≃ₐ[F] KU) M) (hρ : IsOpen (ρ.ker : Set (KU ≃ₐ[F] KU)))
    (n : ℕ) (hM : ∀ m : M, (l ^ n) • m = 0)
    (f : Δ × Δ → M) (hf : IsLocallyConstant f)
    (hc : ∀ g h j : Δ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) :
    ∃ b : Δ → M, IsLocallyConstant b ∧ ∀ g h : Δ, f (g, h) = ρ g (b h) - b (g * h) + b g := by
  classical
  -- the characteristic `p` and `q = p ^ e`
  obtain ⟨p, hpc⟩ := CharP.exists Fq
  obtain ⟨e, hp, hq⟩ := FiniteField.card Fq p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_injective_algebraMap (algebraMap Fq F).injective p
  have he : 0 < (e : ℕ) := e.pos
  -- `K_U = maxUnram`
  have hset : unramSet (FunctionField.ringOfIntegers Fq F) F =
      {L : IntermediateField F (AlgebraicClosure F) | FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (SW39Aux.unram_iff _ F L))
  have hKU' : KU = maxUnram (FunctionField.ringOfIntegers Fq F) F := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have hΔg : Δ ≤ CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq) :=
    fun g hg => (CurveCoh.mem_pi1geo _ _ _ g).2 fun x hx => hΔ g hg x hx
  -- `l` is a unit of `𝔽_q[U]`
  have hlq : (l : Fq) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff Fq p] at h0
    have hpl : p = l := (Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).1 h0
    apply hl
    rw [hq, ← hpl]
    exact dvd_pow_self p (ne_of_gt he)
  have hN : IsUnit ((l : ℕ) : Places.Rfin Fq F) := by
    have h1 : IsUnit ((l : ℕ) : Polynomial Fq) := by
      rw [← Polynomial.C_eq_natCast]
      exact Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hlq)
    have h2 := h1.map (algebraMap (Polynomial Fq) (Places.Rfin Fq F))
    rwa [map_natCast] at h2
  have hPic := Lefschetz.picDivU Fq F l hl
  exact CdOne.h2All_closed (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l hN hPic Δ hΔc hΔg
    Λ n M ρ hM hρ f hf hc
