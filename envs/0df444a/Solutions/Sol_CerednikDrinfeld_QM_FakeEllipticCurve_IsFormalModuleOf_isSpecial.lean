-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleOf.isSpecial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2a44f815-10ca-5d5c-8232-244b4bbecf2d

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_trace_linearPart_addVia_eq_of_isFormalModuleVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal"

open scoped Quaternion

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.IsFormalModuleOf Zp2 FormalODModule FormalODModule.lieZero FormalODModule.lieOne QM.FakeEllipticCurve QM.FakeEllipticCurve.apply_trace_linearPart_addVia_eq_of_isFormalModuleVia"
namespace QM
p2m_export "CerednikDrinfeld.QM" "IsOrderCoord FakeEllipticCurve.IsFormalModuleOf FakeEllipticCurve FakeEllipticCurve.apply_trace_linearPart_addVia_eq_of_isFormalModuleVia"
namespace SpecialOfFEC
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

section Witt

variable (q : ℕ) [Fact q.Prime]

theorem one_lt_q : 1 < q := (Fact.out : q.Prime).one_lt

theorem frobenius_frobenius (c : Zp2 q) : WittVector.frobenius (WittVector.frobenius c) = c := by
  haveI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul]
  have hcard : Fintype.card (GaloisField q 2) = q * q := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card q 2 two_ne_zero, pow_two]
  rw [← hcard, FiniteField.pow_card]

theorem exists_intCast_add_pow_mul (K : ℕ) :
    ∀ c : Zp2 q, WittVector.frobenius c = c → ∃ (n : ℤ) (c' : Zp2 q), c = (n : Zp2 q) + (q : Zp2 q) ^ K * c' := by
  induction K with
  | zero => intro c hc; exact ⟨0, c, by simp⟩
  | succ K ih =>
    intro c hc
    have h0 : (c.coeff 0) ^ q = c.coeff 0 := by
      have := congrArg (fun x : Zp2 q => x.coeff 0) hc
      simpa only [WittVector.coeff_frobenius_charP] using this
    obtain ⟨n₀, hn₀⟩ := (mem_bot_iff_intCast q (GaloisField q 2)).1
      ((Subfield.mem_bot_iff_pow_eq_self (GaloisField q 2) q).2 h0)
    have hmem : c - (n₀ : Zp2 q) ∈ Ideal.span {(q : Zp2 q)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub, map_intCast,
        WittVector.constantCoeff_apply, ← hn₀, sub_self]
    obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton'.1 hmem
    have hc₁f : WittVector.frobenius c₁ = c₁ := by
      have h1 : (WittVector.frobenius c₁ - c₁) * (q : Zp2 q) = 0 := by
        rw [sub_mul, hc₁, ← map_natCast (WittVector.frobenius (p := q) (R := GaloisField q 2)) q, ← map_mul, hc₁,
          map_sub, hc, map_intCast, sub_self]
      exact sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ h1)
    obtain ⟨n₁, c', hc'⟩ := ih c₁ hc₁f
    refine ⟨n₀ + q * n₁, c', ?_⟩
    calc c = (n₀ : Zp2 q) + c₁ * (q : Zp2 q) := by rw [hc₁]; ring
      _ = (n₀ : Zp2 q) + ((n₁ : Zp2 q) + (q : Zp2 q) ^ K * c') * (q : Zp2 q) := by rw [← hc']
      _ = ((n₀ + q * n₁ : ℤ) : Zp2 q) + (q : Zp2 q) ^ (K + 1) * c' := by push_cast; ring

theorem exists_isUnit_sub_frobenius : ∃ ζ : Zp2 q, IsUnit (ζ - WittVector.frobenius ζ) := by
  have hex : ∃ ω : GaloisField q 2, ω ^ q ≠ ω := by
    by_contra hall
    push Not at hall
    have htop : ∀ ω : GaloisField q 2, ω ∈ (⊥ : Subfield (GaloisField q 2)) := fun ω =>
      (Subfield.mem_bot_iff_pow_eq_self (GaloisField q 2) q).2 (hall ω)
    have h1 : Nat.card (⊥ : Subfield (GaloisField q 2)) = Nat.card (GaloisField q 2) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv htop)
    rw [Subfield.card_bot (GaloisField q 2) q, GaloisField.card q 2 two_ne_zero] at h1
    have h2 : q < q ^ 2 := by
      have := one_lt_q q
      nlinarith
    omega
  obtain ⟨ω, hω⟩ := hex
  refine ⟨WittVector.teichmuller q ω, WittVector.isUnit_of_coeff_zero_ne_zero _ ?_⟩
  have hfrob : WittVector.frobenius (WittVector.teichmuller q ω) = WittVector.teichmuller q (ω ^ q) := by
    have := congrFun (congrArg DFunLike.coe (WittVector.frobenius_eq_map_frobenius (p := q) (R := GaloisField q 2)))
      (WittVector.teichmuller q ω)
    rw [this, WittVector.map_teichmuller, frobenius_def]
  rw [hfrob, ← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  exact sub_ne_zero.2 (Ne.symm hω)

theorem frobenius_add_self_fixed (a : Zp2 q) :
    WittVector.frobenius (a + WittVector.frobenius a) = a + WittVector.frobenius a := by
  rw [map_add, frobenius_frobenius, add_comm]

theorem frobenius_mul_self_fixed (a : Zp2 q) :
    WittVector.frobenius (a * WittVector.frobenius a) = a * WittVector.frobenius a := by
  rw [map_mul, frobenius_frobenius, mul_comm]

theorem constantCoeff_natCast_mul (y : Zp2 q) : WittVector.constantCoeff ((q : Zp2 q) * y) = 0 := by
  rw [map_mul, WittVector.constantCoeff_apply, WittVector.coeff_p_zero, zero_mul]

end Witt

section Lie

variable {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B] (X : FormalODModule q B)

def lp : Zp2 q →+* Matrix (Fin 2) (Fin 2) B := (MvFormalGroup.linearPartHom X.F).comp X.actRingHom

theorem lp_apply (a : Zp2 q) : lp X a = MvFormalGroup.linearPart (X.act a) := rfl

theorem lieAct_eq (a : Zp2 q) : X.lieAct a = Matrix.mulVecLin (lp X a) := rfl

abbrev sc : B →+* Matrix (Fin 2) (Fin 2) B := algebraMap B (Matrix (Fin 2) (Fin 2) B)

theorem sc_eq_smul_one (x : B) : sc (B := B) x = x • (1 : Matrix (Fin 2) (Fin 2) B) := Algebra.algebraMap_eq_smul_one x

theorem sc_mul_eq_smul (x : B) (M : Matrix (Fin 2) (Fin 2) B) : sc x * M = x • M := (Algebra.smul_def x M).symm

theorem lp_comm (a a' : Zp2 q) : lp X a * lp X a' = lp X a' * lp X a := by
  rw [← map_mul, mul_comm, map_mul]

theorem sc_comm (x : B) (M : Matrix (Fin 2) (Fin 2) B) : sc x * M = M * sc x := Algebra.commutes x M

theorem commute_lp_lp (a a' : Zp2 q) : Commute (lp X a) (lp X a') := lp_comm X a a'
theorem commute_sc (x : B) (M : Matrix (Fin 2) (Fin 2) B) : Commute (sc x) M := sc_comm x M
theorem commute_sc' (x : B) (M : Matrix (Fin 2) (Fin 2) B) : Commute M (sc x) := (sc_comm x M).symm

theorem lp_pow_eq_zero {K : ℕ} (hK : ((q : ℕ) : B) ^ K = 0) : lp X ((q : Zp2 q) ^ K) = 0 := by
  rw [map_pow, map_natCast, ← map_natCast (sc (B := B)) q, ← map_pow, hK, map_zero]

theorem sc_j_pow_eq_zero (j : Zp2 q →+* B) {K : ℕ} (hK : ((q : ℕ) : B) ^ K = 0) : j ((q : Zp2 q) ^ K) = 0 := by
  rw [map_pow, map_natCast, hK]

variable (j : Zp2 q →+* B) {K : ℕ} (hK : ((q : ℕ) : B) ^ K = 0)
include hK

theorem lp_eq_sc_of_frobenius_eq (c : Zp2 q) (hc : WittVector.frobenius c = c) : lp X c = sc (j c) := by
  obtain ⟨n, c', rfl⟩ := exists_intCast_add_pow_mul q K c hc
  rw [map_add, map_add, map_mul, lp_pow_eq_zero X hK, zero_mul, add_zero, map_add (sc (B := B)), map_mul j,
    sc_j_pow_eq_zero j hK, zero_mul, map_zero, add_zero, map_intCast, map_intCast, map_intCast]

theorem prod_eq_zero (a : Zp2 q) :
    (lp X a - sc (j a)) * (lp X a - sc (j (WittVector.frobenius a))) = 0 := by
  set A := lp X a
  set s1 := sc (B := B) (j a)
  set s2 := sc (B := B) (j (WittVector.frobenius a))
  have h1 : lp X (a + WittVector.frobenius a) = s1 + s2 := by
    rw [lp_eq_sc_of_frobenius_eq X j hK _ (frobenius_add_self_fixed q a), map_add, map_add]
  have h2 : lp X (a * WittVector.frobenius a) = s1 * s2 := by
    rw [lp_eq_sc_of_frobenius_eq X j hK _ (frobenius_mul_self_fixed q a), map_mul, map_mul]
  have hc : A * s2 = s2 * A := (sc_comm _ _).symm
  calc (A - s1) * (A - s2) = A * A - (s1 + s2) * A + s1 * s2 := by rw [sub_mul, mul_sub, mul_sub, hc, add_mul]; abel
    _ = lp X (a * a) - lp X (a + WittVector.frobenius a) * lp X a + lp X (a * WittVector.frobenius a) := by
        rw [h1, h2, map_mul]
    _ = 0 := by
        rw [← map_mul, ← map_sub, ← map_add,
          show a * a - (a + WittVector.frobenius a) * a + a * WittVector.frobenius a = 0 by ring, map_zero]

variable (ζ : Zp2 q) (u : Bˣ) (hu : (u : B) = j ζ - j (WittVector.frobenius ζ))
include hu

def e₀ : Matrix (Fin 2) (Fin 2) B := ((u⁻¹ : Bˣ) : B) • (lp X ζ - sc (j (WittVector.frobenius ζ)))

theorem Zp_sub_Z : (lp X ζ - sc (j (WittVector.frobenius ζ))) - (lp X ζ - sc (j ζ)) = sc (u : B) := by
  rw [hu, map_sub]; abel

theorem Z_mul_Zp : (lp X ζ - sc (j ζ)) * (lp X ζ - sc (j (WittVector.frobenius ζ))) = 0 := prod_eq_zero X j hK ζ

theorem Zp_mul_Z : (lp X ζ - sc (j (WittVector.frobenius ζ))) * (lp X ζ - sc (j ζ)) = 0 := by
  have hcomm : Commute (lp X ζ - sc (j ζ)) (lp X ζ - sc (j (WittVector.frobenius ζ))) :=
    ((Commute.refl _).sub_right (commute_sc' _ _)).sub_left ((commute_sc _ _).sub_right (commute_sc _ _ ))
  rw [← hcomm.eq]; exact Z_mul_Zp X j hK ζ u hu

theorem Zp_mul_Zp : (lp X ζ - sc (j (WittVector.frobenius ζ))) * (lp X ζ - sc (j (WittVector.frobenius ζ))) =
    (u : B) • (lp X ζ - sc (j (WittVector.frobenius ζ))) := by
  have h : lp X ζ - sc (j (WittVector.frobenius ζ)) = (lp X ζ - sc (j ζ)) + sc (u : B) := by
    rw [← Zp_sub_Z X j hK ζ u hu]; abel
  calc (lp X ζ - sc (j (WittVector.frobenius ζ))) * (lp X ζ - sc (j (WittVector.frobenius ζ)))
        = ((lp X ζ - sc (j ζ)) + sc (u : B)) * (lp X ζ - sc (j (WittVector.frobenius ζ))) := by rw [← h]
    _ = (u : B) • (lp X ζ - sc (j (WittVector.frobenius ζ))) := by
        rw [add_mul, Z_mul_Zp X j hK ζ u hu, zero_add, sc_mul_eq_smul]

theorem Z_mul_Z : (lp X ζ - sc (j ζ)) * (lp X ζ - sc (j ζ)) = -((u : B) • (lp X ζ - sc (j ζ))) := by
  have h : lp X ζ - sc (j ζ) = (lp X ζ - sc (j (WittVector.frobenius ζ))) - sc (u : B) := by
    rw [← Zp_sub_Z X j hK ζ u hu]; abel
  calc (lp X ζ - sc (j ζ)) * (lp X ζ - sc (j ζ))
        = ((lp X ζ - sc (j (WittVector.frobenius ζ))) - sc (u : B)) * (lp X ζ - sc (j ζ)) := by rw [← h]
    _ = -((u : B) • (lp X ζ - sc (j ζ))) := by
        rw [sub_mul, Zp_mul_Z X j hK ζ u hu, zero_sub, sc_mul_eq_smul]

theorem e₀_mul_e₀ : e₀ X j ζ u * e₀ X j ζ u = e₀ X j ζ u := by
  rw [e₀, smul_mul_smul_comm, Zp_mul_Zp X j hK ζ u hu, smul_smul, mul_assoc, Units.inv_mul, mul_one]

theorem one_sub_e₀ : 1 - e₀ X j ζ u = -(((u⁻¹ : Bˣ) : B) • (lp X ζ - sc (j ζ))) := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) B) = ((u⁻¹ : Bˣ) : B) • sc (u : B) := by
    rw [sc_eq_smul_one, smul_smul, Units.inv_mul, one_smul]
  rw [e₀, h1, ← smul_sub, ← smul_neg]
  congr 1
  rw [hu, map_sub]; abel

theorem annihilate (a : Zp2 q) :
    (lp X a - sc (j a)) * (lp X ζ - sc (j (WittVector.frobenius ζ))) = 0 ∧
      (lp X a - sc (j (WittVector.frobenius a))) * (lp X ζ - sc (j ζ)) = 0 := by
  set A := lp X a - sc (j a) with hA
  set A' := lp X a - sc (j (WittVector.frobenius a)) with hA'
  set Z := lp X ζ - sc (j ζ) with hZ
  set Z' := lp X ζ - sc (j (WittVector.frobenius ζ)) with hZ'

  have cAZ' : Commute A' Z' :=
    ((commute_lp_lp X a ζ).sub_right (commute_sc' _ _)).sub_left ((commute_sc _ _).sub_right (commute_sc _ _))
  have cZZ' : Commute Z Z' :=
    ((Commute.refl _).sub_right (commute_sc' _ _)).sub_left ((commute_sc _ _).sub_right (commute_sc _ _))
  have cAZ : Commute A Z :=
    ((commute_lp_lp X a ζ).sub_right (commute_sc' _ _)).sub_left ((commute_sc _ _).sub_right (commute_sc _ _))

  have hsum : (A + Z) * (A' + Z') = 0 := by
    have := prod_eq_zero X j hK (a + ζ)
    simp only [map_add] at this
    have e1 : lp X a + lp X ζ - (sc (j a) + sc (j ζ)) = A + Z := by rw [hA, hZ]; abel
    have e2 : lp X a + lp X ζ - (sc (j (WittVector.frobenius a)) + sc (j (WittVector.frobenius ζ))) = A' + Z' := by
      rw [hA', hZ']; abel
    rwa [e1, e2] at this
  have hAA' : A * A' = 0 := prod_eq_zero X j hK a
  have hZZ' : Z * Z' = 0 := Z_mul_Zp X j hK ζ u hu
  have hcross : A * Z' + Z * A' = 0 := by
    have : (A + Z) * (A' + Z') = A * A' + A * Z' + (Z * A' + Z * Z') := by noncomm_ring
    rw [this, hAA', hZZ', zero_add, add_zero] at hsum
    exact hsum
  have hu' : IsUnit (sc (B := B) (u : B)) := (Units.isUnit u).map _
  constructor
  ·
    have h1 : A * Z' * Z' = 0 := by
      have : A * Z' = -(Z * A') := eq_neg_of_add_eq_zero_left hcross
      rw [this, neg_mul, mul_assoc, cAZ'.eq, ← mul_assoc, hZZ', zero_mul, neg_zero]
    rw [mul_assoc, Zp_mul_Zp X j hK ζ u hu, mul_smul_comm, ← sc_mul_eq_smul, (commute_sc _ _).eq] at h1
    exact (hu'.mul_left_eq_zero).1 h1
  ·
    have cA'Z : Commute A' Z :=
      ((commute_lp_lp X a ζ).sub_right (commute_sc' _ _)).sub_left ((commute_sc _ _).sub_right (commute_sc _ _))
    have h1 : Z * Z * A' = 0 := by
      have h2 : Z * A' = -(A * Z') := eq_neg_of_add_eq_zero_right hcross
      rw [mul_assoc, h2, mul_neg, ← mul_assoc, ← cAZ.eq, mul_assoc, hZZ', mul_zero, neg_zero]
    rw [Z_mul_Z X j hK ζ u hu, neg_mul, neg_eq_zero, smul_mul_assoc, ← sc_mul_eq_smul] at h1
    have h3 : Z * A' = 0 := (hu'.mul_right_eq_zero).1 h1
    rw [cA'Z.eq]; exact h3

omit hK hu in
theorem sc_mulVec (x : B) (v : Fin 2 → B) : (sc x).mulVec v = x • v := by
  rw [sc_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

omit hK hu in
theorem mem_lieZero_iff (v : Fin 2 → B) : v ∈ X.lieZero j ↔ ∀ a, (lp X a - sc (j a)).mulVec v = 0 := by
  rw [FormalODModule.lieZero, Submodule.mem_iInf]
  refine forall_congr' fun a => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, lieAct_eq,
    Matrix.mulVecLin_apply, Matrix.sub_mulVec, sc_mulVec]

omit hK hu in
theorem mem_lieOne_iff (v : Fin 2 → B) :
    v ∈ X.lieOne j ↔ ∀ a, (lp X a - sc (j (WittVector.frobenius a))).mulVec v = 0 := by
  rw [FormalODModule.lieOne, Submodule.mem_iInf]
  refine forall_congr' fun a => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, lieAct_eq,
    Matrix.mulVecLin_apply, Matrix.sub_mulVec, sc_mulVec]

theorem lieZero_eq : X.lieZero j = LinearMap.range (Matrix.mulVecLin (e₀ X j ζ u)) := by
  ext v
  rw [mem_lieZero_iff, LinearMap.mem_range]
  constructor
  · intro hv
    refine ⟨v, ?_⟩
    have h1 := hv ζ
    rw [Matrix.sub_mulVec, sc_mulVec, sub_eq_zero] at h1
    rw [Matrix.mulVecLin_apply, e₀, Matrix.smul_mulVec, Matrix.sub_mulVec, h1, sc_mulVec, ← sub_smul, ← hu, smul_smul,
      Units.inv_mul, one_smul]
  · rintro ⟨w, rfl⟩ a
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, e₀, Matrix.mul_smul, (annihilate X j hK ζ u hu a).1, smul_zero,
      Matrix.zero_mulVec]

theorem lieOne_eq : X.lieOne j = LinearMap.range (Matrix.mulVecLin (1 - e₀ X j ζ u)) := by
  ext v
  rw [mem_lieOne_iff, LinearMap.mem_range]
  constructor
  · intro hv
    refine ⟨v, ?_⟩
    have h1 := hv ζ
    rw [Matrix.sub_mulVec, sc_mulVec, sub_eq_zero] at h1
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, e₀, Matrix.smul_mulVec, Matrix.sub_mulVec, h1,
      sc_mulVec, sub_self, smul_zero, sub_zero]
  · rintro ⟨w, rfl⟩ a
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, one_sub_e₀ X j hK ζ u hu, Matrix.mul_neg, Matrix.mul_smul,
      (annihilate X j hK ζ u hu a).2, smul_zero, neg_zero, Matrix.zero_mulVec]

omit hK hu in

theorem trace_e₀ : (e₀ X j ζ u).trace = ((u⁻¹ : Bˣ) : B) * ((lp X ζ).trace - 2 * j (WittVector.frobenius ζ)) := by
  rw [e₀, Matrix.trace_smul, Matrix.trace_sub, sc_eq_smul_one, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul, smul_eq_mul, Nat.cast_ofNat, mul_comm (j _) 2]

end Lie

section TwoByTwo

variable {B : Type} [CommRing B]

theorem mul_self_eq_trace_smul_sub (M : Matrix (Fin 2) (Fin 2) B) : M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) B) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.one_apply, smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem trace_eq_one_and_det_eq_zero (M : Matrix (Fin 2) (Fin 2) B) (hM : M * M = M)
    (hν : IsNilpotent (M.trace - 1)) : M.trace = 1 ∧ M.det = 0 := by
  set ν := M.trace - 1 with hνdef
  have ht : M.trace = ν + 1 := by rw [hνdef]; ring
  have hd2 : IsIdempotentElem M.det := by
    show M.det * M.det = M.det
    rw [← Matrix.det_mul, hM]

  have hkey : M.det • (1 : Matrix (Fin 2) (Fin 2) B) = ν • M := by
    have h := mul_self_eq_trace_smul_sub M
    rw [hM, ht, add_smul, one_smul] at h

    have h2 : M.det • (1 : Matrix (Fin 2) (Fin 2) B) = ν • M + M - M := by
      rw [eq_sub_iff_add_eq] at h
      rw [← h]; abel
    rw [h2]; abel

  have hd_eq : M.det = ν * M 0 0 := by
    have := congrFun (congrFun hkey 0) 0
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  have hdnil : IsNilpotent M.det := by
    rw [hd_eq]; exact Commute.isNilpotent_mul_right (Commute.all _ _) hν
  have hdet : M.det = 0 := by
    obtain ⟨n, hn⟩ := hdnil
    cases n with
    | zero =>
      rw [pow_zero] at hn
      rw [← mul_one M.det, hn, mul_zero]
    | succ n => rw [← hd2.pow_succ_eq n, hn]

  rw [hdet, zero_smul] at hkey
  have h3 : ν * (ν + 1) = 0 := by
    have := congrArg Matrix.trace hkey.symm
    rw [Matrix.trace_smul, Matrix.trace_zero, smul_eq_mul, ht] at this
    exact this
  have hν0 : ν = 0 := (hν.isUnit_add_one.mul_left_eq_zero).1 h3
  refine ⟨?_, hdet⟩
  rw [ht, hν0, zero_add]

end TwoByTwo

section Rank

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]

theorem coord_nsmul (coord : ↥Λ → Zp2 q × Zp2 q) (hadd : ∀ m m' : ↥Λ, coord (m + m') = coord m + coord m')
    (n : ℕ) (m : ↥Λ) : coord (n • m) = n • coord m := by
  induction n with
  | zero =>
    have h := hadd 0 0
    rw [add_zero] at h
    rw [zero_smul, zero_smul]
    exact add_eq_left.mp h.symm
  | succ n ih => rw [succ_nsmul, hadd, ih, succ_nsmul]

theorem linearPart_addVia_act {B : Type} [CommRing B] (X : FormalODModule q B) (α β : Zp2 q) :
    MvFormalGroup.linearPart (Series.addVia X.F (X.act α) ((X.act β).comp X.varpi)) =
      lp X α + lp X β * MvFormalGroup.linearPart X.varpi := by
  have hα : ∀ i, MvPowerSeries.constantCoeff (X.act α i) = 0 := (X.isLawHom_act α).1
  have hβc : ∀ i, MvPowerSeries.constantCoeff (((X.act β).comp X.varpi) i) = 0 :=
    fun i => Series.constantCoeff_comp (X.isLawHom_act β).1 X.isLawHom_varpi.1 i
  rw [show Series.addVia X.F (X.act α) ((X.act β).comp X.varpi) =
      fun i => MvPowerSeries.subst (Sum.elim (X.act α) ((X.act β).comp X.varpi)) (X.F.toPowerSeries i) from rfl,
    MvFormalGroup.linearPart_subst_elim X.F hα hβc,
    show (X.act β).comp X.varpi = fun i => MvPowerSeries.subst X.varpi (X.act β i) from rfl,
    MvFormalGroup.linearPart_subst X.isLawHom_varpi.1]
  rfl

theorem apply_trace_lp_eq (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (j : Zp2 q →+* B) (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    {K : ℕ} (hK : ((q : ℕ) : B) ^ K = 0) (ζ : Zp2 q)
    (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k) :
    sk (lp X ζ).trace = sk (j (ζ + WittVector.frobenius ζ)) := by

  have hqk : ((q : ℕ) : k) = 0 := by
    have : IsNilpotent ((q : ℕ) : k) := ⟨K, by rw [← map_natCast sk, ← map_pow, hK, map_zero]⟩
    exact this.eq_zero
  haveI : CharP k q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).2 hqk

  obtain ⟨m₀, hαm, hβm⟩ := hcoord.dense K ζ 0
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 hαm
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hβm
  have hα' : (coord m₀).1 = ζ + x * (q : Zp2 q) ^ K := by linear_combination -hx
  have hβ' : (coord m₀).2 = y * (q : Zp2 q) ^ K := by rw [← sub_zero (coord m₀).2, ← hy]

  obtain ⟨c, hc⟩ : ∃ c : ℚ, (m₀ : ℍ[ℚ, a, b]) + star (m₀ : ℍ[ℚ, a, b]) = (c : ℍ[ℚ, a, b]) :=
    ⟨_, QuaternionAlgebra.self_add_star' _⟩
  set s : ℕ := c.den with hsdef
  set r : ℤ := c.num with hrdef
  set m₁ : ↥Λ := s • m₀ with hm₁def
  have hm₁ : (m₁ : ℍ[ℚ, a, b]) + star (m₁ : ℍ[ℚ, a, b]) = ((r : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hm₁def, Submodule.coe_smul_of_tower, star_nsmul, ← nsmul_add, hc, nsmul_eq_mul, ← QuaternionAlgebra.coe_natCast,
      ← QuaternionAlgebra.coe_mul, mul_comm, Rat.mul_den_eq_num]
  have hcm₁ : coord m₁ = s • coord m₀ := coord_nsmul coord hcoord.map_add s m₀

  have htr : (s : Zp2 q) * ((coord m₀).1 + WittVector.frobenius (coord m₀).1) = (r : Zp2 q) := by
    have h := hcoord.trace m₁ r hm₁
    rw [hcm₁, Prod.smul_fst, nsmul_eq_mul, map_mul, map_natCast, ← mul_add] at h
    exact h

  have hs : ((s : ℕ) : k) ≠ 0 := by
    intro h0
    have hqs : q ∣ s := (CharP.cast_eq_zero_iff k q s).1 h0
    have ⟨t, ht⟩ := hqs
    have h1 : WittVector.constantCoeff ((r : ℤ) : Zp2 q) = 0 := by
      rw [← htr, ht, Nat.cast_mul, mul_assoc, constantCoeff_natCast_mul]
    rw [map_intCast, CharP.intCast_eq_zero_iff (GaloisField q 2) q] at h1
    have hqr : q ∣ r.natAbs := Int.natCast_dvd.1 h1
    have h1' : q = 1 := Nat.eq_one_of_dvd_coprimes (Rat.reduced c) hqr hqs
    exact (Fact.out : q.Prime).one_lt.ne' h1'

  have hI : ((s : ℕ) : k) * sk (j (ζ + WittVector.frobenius ζ)) = ((r : ℤ) : k) := by
    have hI0 : (s : Zp2 q) * ((coord m₀).1 + WittVector.frobenius (coord m₀).1) =
        (s : Zp2 q) * (ζ + WittVector.frobenius ζ) + (s : Zp2 q) * (x + WittVector.frobenius x) * (q : Zp2 q) ^ K := by
      rw [hα', map_add, map_mul, map_pow, map_natCast]; ring
    have h := congrArg (fun z => sk (j z)) htr
    simp only [hI0, map_add, map_mul, map_pow, map_natCast, map_intCast, hK, mul_zero, add_zero] at h ⊢
    linear_combination h

  have hII : ((s : ℕ) : k) * sk (lp X ζ).trace = ((r : ℤ) : k) := by
    have h3 := CerednikDrinfeld.QM.FakeEllipticCurve.apply_trace_linearPart_addVia_eq_of_isFormalModuleVia
      coord B E X θ hX k sk m₁ r hm₁
    have h1 : lp X (coord m₁).1 = (s : B) • lp X ζ := by
      rw [hcm₁, Prod.smul_fst, hα', nsmul_eq_mul, map_mul, map_natCast, map_add, map_mul, lp_pow_eq_zero X hK,
        mul_zero, add_zero, ← map_natCast (sc (B := B)) s, sc_mul_eq_smul]
    have h2 : lp X (coord m₁).2 = 0 := by
      rw [hcm₁, Prod.smul_snd, hβ', nsmul_eq_mul, map_mul, map_mul, lp_pow_eq_zero X hK, mul_zero, mul_zero]
    have hS : MvFormalGroup.linearPart (Series.addVia X.F (X.act (coord m₁).1) ((X.act (coord m₁).2).comp X.varpi)) =
        (s : B) • lp X ζ := by
      rw [linearPart_addVia_act, h1, h2, zero_mul, add_zero]
    rw [hS, Matrix.trace_smul, smul_eq_mul, map_mul, map_natCast] at h3
    exact h3
  exact mul_left_cancel₀ hs (hII.trans hI.symm)

theorem trace_e₀_sub_one_mem (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (j : Zp2 q →+* B) (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    {K : ℕ} (hK : ((q : ℕ) : B) ^ K = 0) (ζ : Zp2 q) (u : Bˣ) (hu : (u : B) = j ζ - j (WittVector.frobenius ζ))
    (P : Ideal B) (hP : P.IsPrime) : (e₀ X j ζ u).trace - 1 ∈ P := by
  haveI := hP
  let k : Type := AlgebraicClosure (FractionRing (B ⧸ P))
  let sk : B →+* k := ((algebraMap (FractionRing (B ⧸ P)) k).comp (algebraMap (B ⧸ P) (FractionRing (B ⧸ P)))).comp
    (Ideal.Quotient.mk P)
  have hker : ∀ z : B, sk z = 0 ↔ z ∈ P := by
    intro z
    show (algebraMap (FractionRing (B ⧸ P)) k) (algebraMap (B ⧸ P) (FractionRing (B ⧸ P)) (Ideal.Quotient.mk P z)) = 0 ↔ _
    rw [map_eq_zero_iff _ (algebraMap (FractionRing (B ⧸ P)) k).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (B ⧸ P) (FractionRing (B ⧸ P))), Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker, map_sub, map_one, sub_eq_zero, trace_e₀, map_mul, map_sub,
    apply_trace_lp_eq coord hcoord B j E X θ hX hK ζ k sk, map_add, map_add, map_mul, map_ofNat]

  have hu' : sk (j ζ) + sk (j (WittVector.frobenius ζ)) - 2 * sk (j (WittVector.frobenius ζ)) = sk (u : B) := by
    rw [hu, map_sub]; ring
  rw [hu', ← map_mul, Units.inv_mul, map_one]

end Rank

theorem isSpecial {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (j : Zp2 q →+* B)
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B) (hX : E.IsFormalModuleOf coord X) :
    X.IsSpecial j := by
  obtain ⟨K, hK⟩ := hq
  obtain ⟨θ, hXθ⟩ := hX
  obtain ⟨ζ, hζ⟩ := exists_isUnit_sub_frobenius q
  let u : Bˣ := (hζ.map j).unit
  have hu : (u : B) = j ζ - j (WittVector.frobenius ζ) := by rw [IsUnit.unit_spec, map_sub]
  have hidem := e₀_mul_e₀ X j hK ζ u hu
  have hν : IsNilpotent ((e₀ X j ζ u).trace - 1) :=
    nilpotent_iff_mem_prime.2 fun P hP => trace_e₀_sub_one_mem coord hcoord B j E X θ hXθ hK ζ u hu P hP
  obtain ⟨htr, hdet⟩ := trace_eq_one_and_det_eq_zero _ hidem hν
  obtain ⟨-, hc, hi0, hi1⟩ :=
    Matrix.isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero (e₀ X j ζ u) htr hdet
  refine ⟨?_, ?_, ?_⟩
  · rw [lieZero_eq X j hK ζ u hu, lieOne_eq X j hK ζ u hu]; exact hc
  · rw [lieZero_eq X j hK ζ u hu]; exact hi0
  · rw [lieOne_eq X j hK ζ u hu]; exact hi1

end CerednikDrinfeld.QM.SpecialOfFEC

end

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (j : Zp2 q →+* B)
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule q B) (hX : E.IsFormalModuleOf coord X) :
    X.IsSpecial j :=
  CerednikDrinfeld.QM.SpecialOfFEC.isSpecial coord hcoord B hq j E X hX

end S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial (solution)
