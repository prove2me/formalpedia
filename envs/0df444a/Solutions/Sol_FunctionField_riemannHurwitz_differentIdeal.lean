-- Prove2me | solution 1 for FunctionField.riemannHurwitz_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:49:22.734674+00:00
-- url     : https://prove2.me/submissions/351a5ffc-9017-4213-93c7-b65e870b1f17

import Mathlib
import Definitions.Def_RPLib_FX_GOSB_03
import Definitions.Def_RPLib_S3_RRD

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain

namespace UploadGOSB

open RamanujanPetersson.Places (Place Divisor Rfin Rinf Oinf FiniteQuot degS deg)
open RamanujanPetersson.RR RamanujanPetersson.GOS RamanujanPetersson.Places

section Card

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra Fq S] [FiniteQuot S] [Infinite S]

/-- `#(S ⧸ I) = q ^ deg (ordDiv I)` for a nonzero ideal. -/
theorem card_quot_eq_pow_degS {I : Ideal S} (hI : I ≠ ⊥) :
    ∃ n : ℕ, Nat.card (S ⧸ I) = Fintype.card Fq ^ n ∧ degS Fq (ordDiv I) = n := by
  classical
  have key : ∀ s : Finset (HeightOneSpectrum S), (∀ P, ordI P I ≠ 0 → P ∈ s) →
      Nat.card (S ⧸ I) = Fintype.card Fq ^ ∑ P ∈ s, ordI P I * deg Fq P := by
    intro s hs
    have hI0 : I ≠ 0 := hI
    calc Nat.card (S ⧸ I) = cardHom S I := (cardHom_apply I).symm
      _ = (cardHom S : Ideal S →* ℕ) (∏ᶠ v : HeightOneSpectrum S, v.maxPowDividing I) := by
          rw [Ideal.finprod_heightOneSpectrum_factorization hI0]; rfl
      _ = ∏ᶠ v : HeightOneSpectrum S, (cardHom S : Ideal S →* ℕ) (v.maxPowDividing I) :=
          MonoidHom.map_finprod _ (Ideal.hasFiniteMulSupport hI0)
      _ = ∏ v ∈ s, (cardHom S : Ideal S →* ℕ) (v.maxPowDividing I) := by
          apply finprod_eq_prod_of_mulSupport_subset
          intro P hP
          apply hs
          intro h0
          apply hP
          simp only [ordI] at h0
          simp [HeightOneSpectrum.maxPowDividing, h0, ← Ideal.one_eq_top]
      _ = Fintype.card Fq ^ ∑ P ∈ s, ordI P I * deg Fq P := by
          rw [← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_congr rfl fun P _ => ?_
          simp only [MonoidHom.coe_coe, HeightOneSpectrum.maxPowDividing, map_pow, cardHom_apply,
            card_residue_eq Fq P, ← pow_mul, ordI, mul_comm]
  have hfin := finite_ordI_ne_zero hI
  refine ⟨∑ P ∈ hfin.toFinset, ordI P I * deg Fq P,
    key _ fun P hP => (Set.Finite.mem_toFinset _).2 hP, ?_⟩
  unfold degS
  rw [Finsupp.sum_of_support_subset (s := hfin.toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [ordDiv_apply hI]
  · intro P hP
    rw [Finsupp.mem_support_iff, ordDiv_apply hI] at hP
    exact (Set.Finite.mem_toFinset _).2 (by exact_mod_cast hP)
  · intro P _
    simp

end Card

section Main

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem mem_ringOfIntegers_iff (f : F) :
    f ∈ (algebraMap (Rfin Fq F) F).range ↔ f ∈ FunctionField.ringOfIntegers Fq F :=
  ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩

theorem mem_rinf_iff (f : F) :
    f ∈ (algebraMap (Rinf Fq F) F).range ↔ f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring F :=
  ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩

theorem card_LF_poleB (n : ℕ) :
    Nat.card {f : F // f ∈ FunctionField.ringOfIntegers Fq F ∧
      f * (algebraMap Fq[X] F X)⁻¹ ^ n ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring F} =
      Fintype.card Fq ^ ellF Fq F (n • poleB Fq F) := by
  rw [← card_LF]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  rw [mem_LF_poleB, mem_ringOfIntegers_iff, mem_rinf_iff]
  rfl

theorem card_LF_zero :
    Nat.card {f : F // f ∈ FunctionField.ringOfIntegers Fq F ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring F} =
      Fintype.card Fq ^ ellF Fq F 0 := by
  have h := card_LF_poleB Fq F 0
  simp only [pow_zero, mul_one, zero_smul] at h
  exact h

theorem deg_poleB_eq : (poleB Fq F).deg = (Module.finrank (RatFunc Fq) F : ℤ) := by
  rw [← ffData_degD, degD_poleB, ← Module.finrank_eq_card_chooseBasisIndex,
    IsIntegralClosure.rank Fq[X] (RatFunc Fq) F (Rfin Fq F)]

omit [DecidableEq (RatFunc Fq)] in
theorem one_lt_q : 1 < Fintype.card Fq := Fintype.one_lt_card

theorem ellF_zero_eq {e : ℕ}
    (he : Nat.card {f : F // f ∈ FunctionField.ringOfIntegers Fq F ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring F} = Fintype.card Fq ^ e) :
    ellF Fq F 0 = e := by
  rw [card_LF_zero] at he
  exact Nat.pow_right_injective (one_lt_q Fq) he

theorem genusF_eq {g e : ℕ}
    (he : Nat.card {f : F // f ∈ FunctionField.ringOfIntegers Fq F ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring F} = Fintype.card Fq ^ e)
    (hg : ∃ N : ℕ, ∀ n ≥ N, Nat.card {f : F // f ∈ FunctionField.ringOfIntegers Fq F ∧
      f * (algebraMap Fq[X] F X)⁻¹ ^ n ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring F} *
        Fintype.card Fq ^ g = Fintype.card Fq ^ (n * Module.finrank (RatFunc Fq) F + e)) :
    genusF Fq F = g := by
  have he' := ellF_zero_eq Fq F he
  obtain ⟨N, hN⟩ := hg
  set m := Module.finrank (RatFunc Fq) F
  have hm : 0 < m := by
    have := degD_poleB_pos (Fq := Fq) (F := F)
    rw [deg_poleB_eq] at this
    exact_mod_cast this
  set n := N + 2 * genusF Fq F + 1 with hn
  have hdeg : (n • poleB Fq F).deg = (n : ℤ) * m := by
    rw [← ffData_degD, Data.degD_nsmul, ffData_degD, deg_poleB_eq]
  have hlarge : 2 * ((ffData Fq F).genus : ℤ) - 2 * (ffData Fq F).ell 0 < (ffData Fq F).degD (n • poleB Fq F) := by
    rw [ffData_degD, hdeg]
    have : (n : ℤ) ≤ n * m := by
      have : (1 : ℤ) ≤ m := by exact_mod_cast hm
      nlinarith
    have h2 : (2 * (genusF Fq F : ℤ)) < n := by rw [hn]; push_cast; omega
    have h3 : (0 : ℤ) ≤ (ffData Fq F).ell 0 := Int.natCast_nonneg _
    change 2 * (genusF Fq F : ℤ) - 2 * (ffData Fq F).ell 0 < _
    linarith
  have hell := Data.ell_eq_of_large_degD ffData_axioms hlarge
  rw [ffData_degD, hdeg] at hell
  have h1 := hN n (by omega)
  rw [card_LF_poleB, ← pow_add] at h1
  have h2 := Nat.pow_right_injective (one_lt_q Fq) h1
  change (ellF Fq F (n • poleB Fq F) : ℤ) = n * m + ellF Fq F 0 - genusF Fq F at hell
  rw [he'] at hell
  have h3 : ((ellF Fq F (n • poleB Fq F) + g : ℕ) : ℤ) = ((n * m + e : ℕ) : ℤ) := by rw [h2]
  push_cast at h3
  omega

end Main

section Final

open RamanujanPetersson.CupDuality

theorem main
    (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (K : Type*) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
    [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
    [Algebra.IsSeparable (RatFunc Fq) K]
    (L : Type*) [Field L] [Algebra Fq L] [Algebra Fq[X] L] [Algebra (RatFunc Fq) L]
    [IsScalarTower Fq[X] (RatFunc Fq) L] [IsScalarTower Fq Fq[X] L] [FunctionField Fq L]
    [Algebra.IsSeparable (RatFunc Fq) L]
    [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower Fq[X] K L] [IsScalarTower (RatFunc Fq) K L]
    [i1 : Algebra (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)]
    [t1 : IsScalarTower (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L) L]
    [Module.IsTorsionFree (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)]
    [i2 : Algebra (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    [t2 : IsScalarTower (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) L]
    [IsDedekindDomain (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)]
    [IsDedekindDomain (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    [Module.IsTorsionFree (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    (gK gL eK eL d : ℕ)
    (heK : Nat.card {f : K // f ∈ FunctionField.ringOfIntegers Fq K ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring K} = Fintype.card Fq ^ eK)
    (heL : Nat.card {f : L // f ∈ FunctionField.ringOfIntegers Fq L ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring L} = Fintype.card Fq ^ eL)
    (hgK : ∃ N : ℕ, ∀ n ≥ N, Nat.card {f : K // f ∈ FunctionField.ringOfIntegers Fq K ∧
      f * (algebraMap Fq[X] K X)⁻¹ ^ n ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring K} *
        Fintype.card Fq ^ gK = Fintype.card Fq ^ (n * Module.finrank (RatFunc Fq) K + eK))
    (hgL : ∃ N : ℕ, ∀ n ≥ N, Nat.card {f : L // f ∈ FunctionField.ringOfIntegers Fq L ∧
      f * (algebraMap Fq[X] L X)⁻¹ ^ n ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring L} *
        Fintype.card Fq ^ gL = Fintype.card Fq ^ (n * Module.finrank (RatFunc Fq) L + eL))
    (hd : Nat.card (FunctionField.ringOfIntegers Fq L ⧸
        differentIdeal (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)) *
      Nat.card (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L ⧸
        differentIdeal (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
          (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)) = Fintype.card Fq ^ d) :
    2 * (gL : ℤ) - 2 * eL = (Module.finrank K L : ℤ) * (2 * (gK : ℤ) - 2 * eK) + d := by
  have h1 : i1 = algRfin (K := Fq) (F := K) (Y := L) := by
    refine Algebra.algebra_ext _ _ fun a => Subtype.ext ?_
    change ((algebraMap (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L) a :
      FunctionField.ringOfIntegers Fq L) : L) = algebraMap K L a
    exact (IsScalarTower.algebraMap_apply (FunctionField.ringOfIntegers Fq K)
      (FunctionField.ringOfIntegers Fq L) L a).symm
  have h2 : i2 = algRinf (K := Fq) (F := K) (Y := L) := by
    refine Algebra.algebra_ext _ _ fun a => Subtype.ext ?_
    change ((algebraMap (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) a :
      integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) : L) = algebraMap K L a
    exact (IsScalarTower.algebraMap_apply (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) L a).symm
  subst h1 h2
  have hK0 := ellF_zero_eq Fq K heK
  have hL0 := ellF_zero_eq Fq L heL
  have hKg := genusF_eq Fq K heK hgK
  have hLg := genusF_eq Fq L heL hgL
  have hRH := riemannHurwitz Fq K L
  have := finiteDimensional_ff Fq K L
  have := isSeparable_ff Fq K L
  obtain ⟨a, ha, hda⟩ := card_quot_eq_pow_degS Fq
    (differentIdeal_ne_bot' (L := L) (Rfin Fq K) K (Rfin Fq L))
  obtain ⟨b, hb, hdb⟩ := card_quot_eq_pow_degS Fq
    (differentIdeal_ne_bot' (L := L) (Rinf Fq K) K (Rinf Fq L))
  have hdeg : (diffDiv Fq K L).deg = (a : ℤ) + b := by
    rw [diffDiv, Divisor.deg_sumElim, hda, hdb]
  have hab : a + b = d := by
    apply Nat.pow_right_injective (one_lt_q Fq)
    show Fintype.card Fq ^ (a + b) = Fintype.card Fq ^ d
    rw [pow_add, ← ha, ← hb]
    exact hd
  rw [hKg, hLg, hK0, hL0, hdeg] at hRH
  rw [← hab]
  push_cast
  linarith

end Final

end UploadGOSB

theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (K : Type) [Field K] [Algebra Fq K] [Algebra (Polynomial Fq) K] [Algebra (RatFunc Fq) K]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) K] [IsScalarTower Fq (Polynomial Fq) K] [FunctionField Fq K]
    [Algebra.IsSeparable (RatFunc Fq) K]
    (L : Type) [Field L] [Algebra Fq L] [Algebra (Polynomial Fq) L] [Algebra (RatFunc Fq) L]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) L] [IsScalarTower Fq (Polynomial Fq) L] [FunctionField Fq L]
    [Algebra.IsSeparable (RatFunc Fq) L]
    [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower (Polynomial Fq) K L] [IsScalarTower (RatFunc Fq) K L]
    [Algebra (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)]
    [IsScalarTower (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L) L]
    [Module.IsTorsionFree (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)]
    [Algebra (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    [IsScalarTower (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) L]
    [IsDedekindDomain (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)]
    [IsDedekindDomain (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    [Module.IsTorsionFree (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    (gK gL eK eL d : ℕ)
    (heK : Nat.card {f : K // f ∈ FunctionField.ringOfIntegers Fq K ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring K} = Fintype.card Fq ^ eK)
    (heL : Nat.card {f : L // f ∈ FunctionField.ringOfIntegers Fq L ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring L} = Fintype.card Fq ^ eL)
    (hgK : ∃ N : ℕ, ∀ n ≥ N, Nat.card {f : K // f ∈ FunctionField.ringOfIntegers Fq K ∧
      f * (algebraMap (Polynomial Fq) K Polynomial.X)⁻¹ ^ n ∈
        integralClosure (RatFunc.inftyValuation Fq).valuationSubring K} *
        Fintype.card Fq ^ gK = Fintype.card Fq ^ (n * Module.finrank (RatFunc Fq) K + eK))
    (hgL : ∃ N : ℕ, ∀ n ≥ N, Nat.card {f : L // f ∈ FunctionField.ringOfIntegers Fq L ∧
      f * (algebraMap (Polynomial Fq) L Polynomial.X)⁻¹ ^ n ∈
        integralClosure (RatFunc.inftyValuation Fq).valuationSubring L} *
        Fintype.card Fq ^ gL = Fintype.card Fq ^ (n * Module.finrank (RatFunc Fq) L + eL))
    (hd : Nat.card (FunctionField.ringOfIntegers Fq L ⧸
        differentIdeal (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)) *
      Nat.card (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L ⧸
        differentIdeal (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
          (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)) = Fintype.card Fq ^ d) :
    2 * (gL : ℤ) - 2 * eL = (Module.finrank K L : ℤ) * (2 * (gK : ℤ) - 2 * eK) + d := by
  exact UploadGOSB.main Fq K L gK gL eK eL d heK heL hgK hgL hd
