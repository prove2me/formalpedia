-- Prove2me | solution 1 for FreyPackage.frey_exists_decomposition_branch_swap_of_a_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3115bead-99d4-579b-8552-aa34ec48b509

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_FreyPackage_freyCurveInt_discr_ne_zero
import Theorems.Thm_FreyPackage_dvd_freyCurveInt_discr_iff
import Theorems.Thm_FreyPackage_not_dvd_freyCurveInt_c4
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Theorems.Thm_WeierstrassCurve_slope_mem_of_shallow
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_of_not_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_ValuationSubring_residue_ne_zero_iff_valuation_eq_one
import Theorems.Thm_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (P : FreyPackage) (h8 : (P.a : ZMod 8) = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ σ ∈ A.decompositionSubgroup ℚ,
      ∀ x : Submodule.torsionBy ℤ
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
        ¬ P.freyCurveInt.InZeroComponentAt A
            (x : ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) →
          P.freyCurveInt.InZeroComponentAt A
            ((σ • x + x :
              Submodule.torsionBy ℤ
                ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p) :
              ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by
  classical

  have hΔ0 : P.freyCurveInt.Δ ≠ 0 := P.freyCurveInt_discr_ne_zero
  have habc : (2 : ℤ) ∣ P.a * P.b * P.c := P.two_dvd_abc
  have h2Δ : ((2 : ℕ) : ℤ) ∣ P.freyCurveInt.Δ :=
    (P.dvd_freyCurveInt_discr_iff Nat.prime_two).mpr (by exact_mod_cast habc)
  have h2c₄ : ¬ ((2 : ℕ) : ℤ) ∣ P.freyCurveInt.c₄ :=
    P.not_dvd_freyCurveInt_c4 Nat.prime_two (by exact_mod_cast habc)

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, -⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction
      P.freyCurveInt Nat.prime_two hΔ0 h2Δ h2c₄ A hA

  obtain ⟨σ, hφ⟩ :=
    ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  have hσD : σ ∈ A.decompositionSubgroup ℚ := hφ.mem_decompositionSubgroup
  have hvmap : ∀ z : AlgebraicClosure ℚ, A.valuation (σ z) = A.valuation z := fun z =>
    ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A hσD z

  have hv2 : A.valuation ((2 : ℕ) : AlgebraicClosure ℚ) < 1 := hA
  have hv2' : A.valuation (2 : AlgebraicClosure ℚ) < 1 := by
    have h : (((2 : ℕ)) : AlgebraicClosure ℚ) = (2 : AlgebraicClosure ℚ) := by norm_cast
    rwa [h] at hv2
  have h2A : (2 : AlgebraicClosure ℚ) ∈ A :=
    ValuationSubring.mem_of_valuation_le_one A _ hv2'.le
  have h3A : (3 : AlgebraicClosure ℚ) ∈ A := by exact_mod_cast natCast_mem A 3
  have hvle : ∀ {z : AlgebraicClosure ℚ}, z ∈ A → A.valuation z ≤ 1 := fun hz =>
    A.valuation_le_one ⟨_, hz⟩
  have hsmall : ∀ {w : AlgebraicClosure ℚ}, w ∈ A → A.valuation (2 * w) < 1 := by
    intro w hw
    calc A.valuation (2 * w) = A.valuation 2 * A.valuation w := map_mul A.valuation 2 w
      _ ≤ A.valuation 2 * 1 := mul_le_mul_right (hvle hw) _
      _ = A.valuation 2 := mul_one _
      _ < 1 := hv2'

  have hres0 : ∀ {z : AlgebraicClosure ℚ} (hz : z ∈ A), A.valuation z < 1 →
      IsLocalRing.residue A ⟨z, hz⟩ = 0 := by
    intro z hz hlt
    by_contra hne
    exact absurd ((ValuationSubring.residue_ne_zero_iff_valuation_eq_one A hz).mp hne) hlt.ne
  have hres1 : ∀ {z : AlgebraicClosure ℚ} (hz : z ∈ A),
      IsLocalRing.residue A ⟨z, hz⟩ ≠ 0 → A.valuation z = 1 := fun hz hne =>
    (ValuationSubring.residue_ne_zero_iff_valuation_eq_one A hz).mp hne

  have hca₁ : ((P.freyCurveInt.a₁ : ℤ) : AlgebraicClosure ℚ) = 1 := by
    rw [show P.freyCurveInt.a₁ = 1 from rfl]; exact Int.cast_one
  have hca₃ : ((P.freyCurveInt.a₃ : ℤ) : AlgebraicClosure ℚ) = 0 := by
    rw [show P.freyCurveInt.a₃ = 0 from rfl]; exact Int.cast_zero
  have ha₂A : ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A _
  have ha₄A : ((P.freyCurveInt.a₄ : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A _
  have hFy' : 2 * y₀ + x₀ = 0 := by
    have h := hFy
    rw [hca₁, hca₃] at h
    linear_combination h
  have hFx' : y₀ = 3 * x₀ ^ 2 + 2 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) * x₀
      + ((P.freyCurveInt.a₄ : ℤ) : AlgebraicClosure ℚ) := by
    have h := hFx
    rw [hca₁] at h
    linear_combination h

  have hcrit : 6 * x₀ ^ 2 + (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1) * x₀
      + 2 * ((P.freyCurveInt.a₄ : ℤ) : AlgebraicClosure ℚ) = 0 := by
    linear_combination hFy' - 2 * hFx'

  have hv4a₂ : A.valuation (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ)) < 1 := by
    have h : (4 : AlgebraicClosure ℚ) * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ)
        = 2 * (2 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ)) := by ring
    rw [h]; exact hsmall (mul_mem h2A ha₂A)
  have hNA : (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1) ∈ A :=
    add_mem (mul_mem (by exact_mod_cast natCast_mem A 4) ha₂A) (one_mem A)
  have h1A : (1 : AlgebraicClosure ℚ) ∈ A := one_mem A
  have hresN : IsLocalRing.residue A ⟨_, hNA⟩ = 1 := by
    have heq : IsLocalRing.residue A ⟨_, hNA⟩ = IsLocalRing.residue A ⟨1, h1A⟩ :=
      (ValuationSubring.residue_eq_residue_iff_valuation_sub_lt_one A hNA h1A).mpr (by
        have h : (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1) - 1
            = 4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) := by ring
        rw [h]; exact hv4a₂)
    rw [heq, show (⟨(1 : AlgebraicClosure ℚ), h1A⟩ : A) = 1 from rfl, map_one]
  have hvN : A.valuation (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1) = 1 :=
    hres1 hNA (by rw [hresN]; exact one_ne_zero)

  have hrel : (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1) * x₀
      = -(6 * x₀ ^ 2 + 2 * ((P.freyCurveInt.a₄ : ℤ) : AlgebraicClosure ℚ)) := by
    linear_combination hcrit
  have hvx₀ : A.valuation x₀ < 1 := by
    have h6 : A.valuation (6 * x₀ ^ 2 + 2 * ((P.freyCurveInt.a₄ : ℤ) : AlgebraicClosure ℚ)) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · have h : (6 : AlgebraicClosure ℚ) * x₀ ^ 2 = 2 * (3 * x₀ ^ 2) := by ring
        rw [h]; exact hsmall (mul_mem h3A (pow_mem hx₀ 2))
      · exact hsmall ha₄A
    have h := congrArg A.valuation hrel
    rw [map_mul, hvN, one_mul, Valuation.map_neg] at h
    rw [h]; exact h6
  have hresx₀ : IsLocalRing.residue A ⟨x₀, hx₀⟩ = 0 := hres0 hx₀ hvx₀

  have h4dvd : (4 : ℤ) ∣ P.b ^ P.p - 1 - P.a ^ P.p := by
    have hb4 : ((P.b : ZMod 4)) ^ P.p = 0 := by
      obtain ⟨γ, hγ⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).mp P.hb2
      obtain ⟨j, hj⟩ : ∃ j, P.p = 2 + j := ⟨P.p - 2, by have := P.hp5; omega⟩
      have hcast : (P.b : ZMod 4) = 2 * (γ : ZMod 4) := by rw [hγ]; push_cast; ring
      rw [hcast, hj, pow_add, mul_pow, show ((2 : ZMod 4)) ^ 2 = 0 from by decide,
        zero_mul, zero_mul]
    have ha4' : ((P.a : ZMod 4)) ^ P.p = 3 := by
      obtain ⟨m, hm⟩ := P.hp_odd
      rw [P.ha4, hm, pow_succ, pow_mul, show ((3 : ZMod 4)) ^ 2 = 1 from by decide,
        one_pow, one_mul]
    have h0 : ((P.b ^ P.p - 1 - P.a ^ P.p : ℤ) : ZMod 4) = 0 := by
      push_cast
      rw [hb4, ha4']
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h0
  have hmod8 : ((P.b ^ P.p - 1 - P.a ^ P.p : ℤ) : ZMod 8) = 4 := by
    have hb8 : ((P.b : ZMod 8)) ^ P.p = 0 := by
      obtain ⟨γ, hγ⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).mp P.hb2
      obtain ⟨j, hj⟩ : ∃ j, P.p = 3 + j := ⟨P.p - 3, by have := P.hp5; omega⟩
      have hcast : (P.b : ZMod 8) = 2 * (γ : ZMod 8) := by rw [hγ]; push_cast; ring
      rw [hcast, hj, pow_add, mul_pow, show ((2 : ZMod 8)) ^ 3 = 0 from by decide,
        zero_mul, zero_mul]
    have ha8 : ((P.a : ZMod 8)) ^ P.p = 3 := by
      obtain ⟨m, hm⟩ := P.hp_odd
      rw [h8, hm, pow_succ, pow_mul, show ((3 : ZMod 8)) ^ 2 = 1 from by decide,
        one_pow, one_mul]
    push_cast
    rw [hb8, ha8]
    decide
  have hodd : ¬ (2 : ℤ) ∣ P.freyCurveInt.a₂ := by
    rintro ⟨t, ht⟩
    have h4 : P.freyCurveInt.a₂ * 4 = P.b ^ P.p - 1 - P.a ^ P.p := by
      show (P.b ^ P.p - 1 - P.a ^ P.p) / 4 * 4 = _
      exact Int.ediv_mul_cancel h4dvd
    have h8dvd : (8 : ℤ) ∣ P.b ^ P.p - 1 - P.a ^ P.p := ⟨t, by rw [← h4, ht]; ring⟩
    have h0 : ((P.b ^ P.p - 1 - P.a ^ P.p : ℤ) : ZMod 8) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr (by exact_mod_cast h8dvd)
    rw [hmod8] at h0
    exact absurd h0 (by decide)
  have ha₂odd : ∃ t : ℤ, P.freyCurveInt.a₂ = 2 * t + 1 := by
    rcases Int.even_or_odd P.freyCurveInt.a₂ with h | h
    · obtain ⟨k, hk⟩ := h
      exact absurd ⟨k, by omega⟩ hodd
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, hk⟩
  have hresa₂ : IsLocalRing.residue A ⟨((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ), ha₂A⟩
      = 1 := by
    obtain ⟨t, ht⟩ := ha₂odd
    have heq : IsLocalRing.residue A ⟨((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ), ha₂A⟩
        = IsLocalRing.residue A ⟨1, h1A⟩ :=
      (ValuationSubring.residue_eq_residue_iff_valuation_sub_lt_one A ha₂A h1A).mpr (by
        have h : ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) - 1
            = 2 * ((t : ℤ) : AlgebraicClosure ℚ) := by rw [ht]; push_cast; ring
        rw [h]; exact hsmall (intCast_mem A t))
    rw [heq, show (⟨(1 : AlgebraicClosure ℚ), h1A⟩ : A) = 1 from rfl, map_one]

  have hσcrit : 6 * (σ x₀) ^ 2 + (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1) * (σ x₀)
      + 2 * ((P.freyCurveInt.a₄ : ℤ) : AlgebraicClosure ℚ) = 0 := by
    have h0 := congrArg σ hcrit
    simp only [map_add, map_mul, map_pow, map_ofNat, map_intCast, map_one,
      _root_.map_zero] at h0
    linear_combination h0
  have hσx₀ : σ x₀ = x₀ := by
    have hfact : (x₀ - σ x₀) *
        (6 * (x₀ + σ x₀) + (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1)) = 0 := by
      linear_combination hcrit - hσcrit
    rcases mul_eq_zero.mp hfact with h | h
    · exact (sub_eq_zero.mp h).symm
    · exfalso
      have hmem : σ x₀ ∈ A :=
        ValuationSubring.mem_of_valuation_le_one A _ (by rw [hvmap x₀]; exact hvle hx₀)
      have hval : A.valuation (6 * (x₀ + σ x₀)) < 1 := by
        have h6 : (6 : AlgebraicClosure ℚ) * (x₀ + σ x₀) = 2 * (3 * (x₀ + σ x₀)) := by ring
        rw [h6]; exact hsmall (mul_mem h3A (add_mem hx₀ hmem))
      have heq : (4 * ((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 1)
          = -(6 * (x₀ + σ x₀)) := by linear_combination h
      rw [heq, Valuation.map_neg] at hvN
      exact hval.ne hvN
  have hσy₀ : σ y₀ = y₀ := by
    have h0 := congrArg σ hFy'
    simp only [map_add, map_mul, map_ofNat, _root_.map_zero] at h0
    rw [hσx₀] at h0
    have h2 : (2 : AlgebraicClosure ℚ) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h2 (by linear_combination h0 - hFy')

  have h11 : ((1 : IsLocalRing.ResidueField A) + 1) = 0 := by
    have h2r : IsLocalRing.residue A ⟨(2 : AlgebraicClosure ℚ), h2A⟩ = 0 := hres0 h2A hv2'
    have hmk : (⟨(2 : AlgebraicClosure ℚ), h2A⟩ : A) = 1 + 1 :=
      Subtype.ext (by push_cast; norm_num)
    rw [hmk, map_add, map_one] at h2r
    exact h2r

  refine ⟨σ, hσD, ?_⟩
  intro x hout
  rcases hP : (x : ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    with _ | ⟨x₁, y₁, h₁⟩
  ·
    exact absurd (Or.inl hP) hout

  rw [hP] at hout
  have hX : A.valuation (x₁ - x₀) < 1 :=
    (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre
      P.freyCurveInt A hx₀ hy₀ hFy hFx hnode hbad h₁).mp hout

  have hx2 := x.2
  rw [Submodule.mem_torsionBy_iff] at hx2
  rw [hP] at hx2
  have htor : P.p • (Point.some x₁ y₁ h₁ :
      ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
    rwa [natCast_zsmul] at hx2

  have hp2 : P.p ≠ 2 := by have := P.hp5; omega
  obtain ⟨hshΔ, -⟩ :=
    WeierstrassCurve.valuation_pow_eq_of_torsion_of_not_inZeroComponentAt
      P.freyCurveInt Nat.prime_two hΔ0 h2Δ h2c₄ A hA hx₀ hy₀ hFy hFx hnode hbad
      P.pp hp2 hp2 h₁ htor hX
  have hΔF := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre
    P.freyCurveInt A hx₀ hy₀ hFy hFx hnode hbad
  rw [hΔF] at hshΔ

  obtain ⟨hΛA, -, hquadv⟩ :=
    WeierstrassCurve.slope_mem_of_shallow P.freyCurveInt A hx₀ hy₀ hFy hFx h₁ hX hshΔ
  set lam : AlgebraicClosure ℚ := (y₁ - y₀) / (x₁ - x₀) with hlam
  rw [hca₁, one_mul] at hquadv

  have hzA : lam ^ 2 + lam - (((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 3 * x₀) ∈ A :=
    sub_mem (add_mem (pow_mem hΛA 2) hΛA) (add_mem ha₂A (mul_mem h3A hx₀))
  have hresz : IsLocalRing.residue A ⟨_, hzA⟩ = 0 := hres0 hzA hquadv
  have hzeq : (⟨lam ^ 2 + lam - (((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ) + 3 * x₀),
      hzA⟩ : A) = ⟨lam, hΛA⟩ ^ 2 + ⟨lam, hΛA⟩
        - (⟨((P.freyCurveInt.a₂ : ℤ) : AlgebraicClosure ℚ), ha₂A⟩
          + ⟨(3 : AlgebraicClosure ℚ), h3A⟩ * ⟨x₀, hx₀⟩) := by
    refine Subtype.ext ?_
    push_cast
    ring
  rw [hzeq] at hresz
  simp only [map_sub, map_add, map_mul, map_pow, hresa₂, hresx₀, mul_zero, add_zero] at hresz

  have hΛσA : σ lam ∈ A :=
    ValuationSubring.mem_of_valuation_le_one A _ (by rw [hvmap]; exact hvle hΛA)
  have hgsmul : (⟨σ, hσD⟩ : A.decompositionSubgroup ℚ) • (⟨lam, hΛA⟩ : A)
      = ⟨σ lam, hΛσA⟩ := rfl
  have hresσΛ : IsLocalRing.residue A ⟨σ lam, hΛσA⟩
      = (IsLocalRing.residue A ⟨lam, hΛA⟩) ^ 2 := by
    rw [← hgsmul, IsLocalRing.ResidueField.residue_smul]
    exact hφ.smul_residue_eq _

  have hrne : IsLocalRing.residue A ⟨σ lam, hΛσA⟩ - IsLocalRing.residue A ⟨lam, hΛA⟩ ≠ 0 := by
    rw [hresσΛ]
    intro hrr
    have h1 : (IsLocalRing.residue A ⟨lam, hΛA⟩) ^ 2 = IsLocalRing.residue A ⟨lam, hΛA⟩ :=
      sub_eq_zero.mp hrr
    have h10 : (1 : IsLocalRing.ResidueField A) = 0 := by
      linear_combination -hresz + h1 + IsLocalRing.residue A ⟨lam, hΛA⟩ * h11
    exact one_ne_zero h10
  have hsubA : σ lam - lam ∈ A := sub_mem hΛσA hΛA
  have hbr0 : A.valuation (σ lam - lam) = 1 := by
    apply hres1 hsubA
    have hmk : (⟨σ lam - lam, hsubA⟩ : A) = ⟨σ lam, hΛσA⟩ - ⟨lam, hΛA⟩ := rfl
    rw [hmk, map_sub]
    exact hrne

  have hlev : A.valuation (σ x₁ - x₀) = A.valuation (x₁ - x₀) := by
    rw [show σ x₁ - x₀ = σ (x₁ - x₀) by rw [map_sub, hσx₀], hvmap]
  have hXσ : A.valuation (σ x₁ - x₀) < 1 := by rw [hlev]; exact hX
  have hσlam : σ lam = (σ y₁ - y₀) / (σ x₁ - x₀) := by
    rw [hlam, map_div₀, map_sub, map_sub, hσx₀, hσy₀]
  have hbr : A.valuation ((σ y₁ - y₀) / (σ x₁ - x₀) - (y₁ - y₀) / (x₁ - x₀)) = 1 := by
    rw [← hσlam, ← hlam]
    exact hbr0

  obtain ⟨hns, hσsome⟩ : ∃ hns :
      ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular
        (σ x₁) (σ y₁),
      σ • (Point.some x₁ y₁ h₁ :
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = Point.some (σ x₁) (σ y₁) hns :=
    ⟨_, Point.map_some σ.toAlgHom h₁⟩

  have hcloser :=
    WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne
      P.freyCurveInt A hx₀ hy₀ hFy hFx hnode hbad hns h₁ hXσ hX hlev
      (by rw [hlev]; exact hshΔ) hbr
  have hcoe : ((σ • x + x :
      Submodule.torsionBy ℤ
        ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p) :
      ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
      = Point.some (σ x₁) (σ y₁) hns + Point.some x₁ y₁ h₁ := by
    calc ((σ • x + x :
        Submodule.torsionBy ℤ
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p) :
        ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
        = σ • (x : ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
          + (x : ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := rfl
      _ = Point.some (σ x₁) (σ y₁) hns + Point.some x₁ y₁ h₁ := by rw [hP, hσsome]
  rw [hcoe]
  exact hcloser.1

end S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight
end P2MW
export P2MW.S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight (solution)
