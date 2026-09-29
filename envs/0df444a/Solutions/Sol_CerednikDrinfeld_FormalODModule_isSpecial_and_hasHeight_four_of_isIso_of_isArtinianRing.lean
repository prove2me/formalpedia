-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/76312744-d708-542a-9a72-5895ec3ed406

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Theorems.Thm_MvPowerSeries_finite_free_finrank_quotient_span_eq_of_isArtinianRing_of_finite_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff subst_comp_subst_apply
  subst_X map_subst)
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

noncomputable section

namespace R4AutoSH

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
  · have h1 : A * Z' * Z' = 0 := by
      have : A * Z' = -(Z * A') := eq_neg_of_add_eq_zero_left hcross
      rw [this, neg_mul, mul_assoc, cAZ'.eq, ← mul_assoc, hZZ', zero_mul, neg_zero]
    rw [mul_assoc, Zp_mul_Zp X j hK ζ u hu, mul_smul_comm, ← sc_mul_eq_smul, (commute_sc _ _).eq] at h1
    exact (hu'.mul_left_eq_zero).1 h1
  · have cA'Z : Commute A' Z :=
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

theorem mul_self_eq_trace_smul_sub (M : Matrix (Fin 2) (Fin 2) B) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) B) := by
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

theorem trace_eq_one_of_finrank {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K) (hM : M * M = M)
    (h0 : Module.finrank K (LinearMap.range (Matrix.mulVecLin M)) = 1)
    (h1 : Module.finrank K (LinearMap.range (Matrix.mulVecLin (1 - M))) = 1) : M.trace = 1 := by
  by_contra htr
  have hCH := mul_self_eq_trace_smul_sub M
  rw [hM] at hCH
  have hdet2 : M.det * M.det = M.det := by rw [← Matrix.det_mul, hM]
  by_cases hd : M.det = 0
  · have hsm : (M.trace - 1) • M = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      conv_rhs => rw [hCH]
      rw [hd, zero_smul, sub_zero]
    have hM0 : M = 0 := by
      rcases smul_eq_zero.1 hsm with h | h
      · exact absurd (sub_eq_zero.1 h) htr
      · exact h
    rw [hM0, Matrix.mulVecLin_zero, LinearMap.range_zero, finrank_bot] at h0
    exact zero_ne_one h0
  · have hd1 : M.det = 1 := by
      have : M.det * M.det = 1 * M.det := by rw [hdet2, one_mul]
      exact mul_right_cancel₀ hd this
    have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (hd1 ▸ isUnit_one)
    obtain ⟨v, hv⟩ := hMu
    have hM1 : M = 1 := by
      have := congrArg (fun N => N * ((v⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K)) hM
      rw [← hv] at this ⊢
      rw [mul_assoc, Units.mul_inv, mul_one] at this
      exact this
    rw [hM1, sub_self, Matrix.mulVecLin_zero, LinearMap.range_zero, finrank_bot] at h1
    exact zero_ne_one h1

end TwoByTwo

section Transport

variable {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B] {B' : Type} [CommRing B']

theorem linearPart_map (f : B →+* B') (φ : Series B) :
    MvFormalGroup.linearPart (φ.map f) = (MvFormalGroup.linearPart φ).map f := by
  ext i j
  simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.map_apply, Series.map, MvPowerSeries.coeff_map]

theorem lp_map (f : B →+* B') (X : FormalODModule q B) (a : Zp2 q) : lp (X.map f) a = (lp X a).map f :=
  linearPart_map f (X.act a)

theorem trace_lp_map (f : B →+* B') (X : FormalODModule q B) (a : Zp2 q) :
    (lp (X.map f) a).trace = f (lp X a).trace := by
  rw [lp_map, Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.map_apply, Matrix.map_apply, map_add]

def eig (X : FormalODModule q B) (t : Zp2 q → B) : Submodule B (Fin 2 → B) :=
  ⨅ a : Zp2 q, LinearMap.ker (X.lieAct a - t a • LinearMap.id)

theorem lieZero_eq_eig (X : FormalODModule q B) (j : Zp2 q →+* B) : X.lieZero j = eig X (fun a => j a) := rfl

theorem lieOne_eq_eig (X : FormalODModule q B) (j : Zp2 q →+* B) :
    X.lieOne j = eig X (fun a => j (WittVector.frobenius a)) := rfl

theorem mem_eig_iff (X : FormalODModule q B) (t : Zp2 q → B) (v : Fin 2 → B) :
    v ∈ eig X t ↔ ∀ a, (lp X a - sc (t a)).mulVec v = 0 := by
  rw [eig, Submodule.mem_iInf]
  refine forall_congr' fun a => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, lieAct_eq,
    Matrix.mulVecLin_apply, Matrix.sub_mulVec, sc_mulVec]

theorem linearPart_comp (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (ψ.comp φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem linearPart_id : MvFormalGroup.linearPart (Series.id B) = 1 := MvFormalGroup.linearPart_X

theorem lp_intertwine {X Y : FormalODModule q B} (w : X.Hom Y) (a : Zp2 q) :
    MvFormalGroup.linearPart w.toSeries * lp X a = lp Y a * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart (w.isODHom.2.1 a)
  rw [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ w.isODHom.constantCoeff] at h
  exact h

theorem nonempty_eig_equiv {X Y : FormalODModule q B} (w : X.Hom Y) (hw : w.IsIso) (t : Zp2 q → B) :
    Nonempty (eig X t ≃ₗ[B] eig Y t) := by
  obtain ⟨g, hgw, hwg⟩ := hw
  set W := MvFormalGroup.linearPart w.toSeries
  set G := MvFormalGroup.linearPart g.toSeries
  have hGW : G * W = 1 := by
    have h := congrArg (fun f : X.Hom X => MvFormalGroup.linearPart f.toSeries) hgw
    rw [show (g.comp w).toSeries = g.toSeries.comp w.toSeries from rfl,
      linearPart_comp _ _ w.isODHom.constantCoeff] at h
    rw [h]; exact linearPart_id
  have hWG : W * G = 1 := by
    have h := congrArg (fun f : Y.Hom Y => MvFormalGroup.linearPart f.toSeries) hwg
    rw [show (w.comp g).toSeries = w.toSeries.comp g.toSeries from rfl,
      linearPart_comp _ _ g.isODHom.constantCoeff] at h
    rw [h]; exact linearPart_id
  have hmapW : ∀ v ∈ eig X t, Matrix.mulVecLin W v ∈ eig Y t := by
    intro v hv
    rw [mem_eig_iff] at hv ⊢
    intro a
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, sub_mul, sc_comm, ← lp_intertwine w a, ← mul_sub,
      ← Matrix.mulVec_mulVec, hv a, Matrix.mulVec_zero]
  have hmapG : ∀ v ∈ eig Y t, Matrix.mulVecLin G v ∈ eig X t := by
    intro v hv
    rw [mem_eig_iff] at hv ⊢
    intro a
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, sub_mul, sc_comm, ← lp_intertwine g a, ← mul_sub,
      ← Matrix.mulVec_mulVec, hv a, Matrix.mulVec_zero]
  refine ⟨LinearEquiv.ofLinear ((Matrix.mulVecLin W).restrict hmapW) ((Matrix.mulVecLin G).restrict hmapG) ?_ ?_⟩
  · ext ⟨v, hv⟩ i
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrict_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hWG, Matrix.one_mulVec, LinearMap.id_coe, id_eq]
  · ext ⟨v, hv⟩ i
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrict_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hGW, Matrix.one_mulVec, LinearMap.id_coe, id_eq]

theorem isIso_map {X Y : FormalODModule q B} (w : X.Hom Y) (hw : w.IsIso) (f : B →+* B') : (w.map f).IsIso := by
  obtain ⟨g, hgw, hwg⟩ := hw
  refine ⟨g.map f, ?_, ?_⟩
  · apply FormalODModule.Hom.ext
    show (g.toSeries.map f).comp (w.toSeries.map f) = Series.id B'
    rw [← Series.map_comp f _ _ w.isODHom.constantCoeff, show g.toSeries.comp w.toSeries = (g.comp w).toSeries from rfl,
      hgw]
    exact Series.map_id f
  · apply FormalODModule.Hom.ext
    show (w.toSeries.map f).comp (g.toSeries.map f) = Series.id B'
    rw [← Series.map_comp f _ _ g.isODHom.constantCoeff, show w.toSeries.comp g.toSeries = (w.comp g).toSeries from rfl,
      hwg]
    exact Series.map_id f

end Transport

section KerAlg

variable {B : Type} [CommRing B]

theorem subst_mem_span (φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) (h : MvPowerSeries (Fin 2) B)
    (hh : constantCoeff h = 0) : subst φ h ∈ Ideal.span (Set.range φ) := by
  have hφ' : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  have h1 : h ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) := by
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker, hh]
  have h2 : subst φ h ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))).map
      (MvPowerSeries.substAlgHom (R := B) hφ').toRingHom := by
    rw [← MvPowerSeries.substAlgHom_apply hφ']
    exact Ideal.mem_map_of_mem _ h1
  rw [Ideal.map_span] at h2
  convert h2 using 2
  ext y
  simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPowerSeries.substAlgHom_apply, subst_X hφ']

theorem span_comp_le (w ψ : Series B) (hw : ∀ i, constantCoeff (w i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    Ideal.span (Set.range (w.comp ψ)) ≤ Ideal.span (Set.range ψ) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact subst_mem_span ψ hψ (w i) (hw i)

variable {q : ℕ} [Fact q.Prime]

theorem nonempty_kerAlgebra_equiv (X Y : FormalODModule q B) (w : X.Hom Y) (hw : w.IsIso) (a : Zp2 q) :
    Nonempty (FormalODModule.KerAlgebra (Y.act a) ≃ₐ[B] FormalODModule.KerAlgebra (X.act a)) := by
  obtain ⟨g, hgw, hwg⟩ := hw
  have hw0 := w.isODHom.constantCoeff
  have hg0 := g.isODHom.constantCoeff
  have hw' : HasSubst w.toSeries := hasSubst_of_constantCoeff_zero hw0
  have hg' : HasSubst g.toSeries := hasSubst_of_constantCoeff_zero hg0
  let Sw : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2) B := MvPowerSeries.substAlgHom (R := B) hw'
  let Sg : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2) B := MvPowerSeries.substAlgHom (R := B) hg'
  have hwg' : (fun s => subst g.toSeries (w.toSeries s)) = Series.id B := congrArg FormalODModule.Hom.toSeries hwg
  have hgw' : (fun s => subst w.toSeries (g.toSeries s)) = Series.id B := congrArg FormalODModule.Hom.toSeries hgw
  have h1 : ∀ h, Sg (Sw h) = h := fun h => by
    simp only [Sw, Sg, MvPowerSeries.substAlgHom_apply]
    rw [subst_comp_subst_apply hw' hg', hwg']
    exact congrFun MvPowerSeries.subst_self h
  have h2 : ∀ h, Sw (Sg h) = h := fun h => by
    simp only [Sw, Sg, MvPowerSeries.substAlgHom_apply]
    rw [subst_comp_subst_apply hg' hw', hgw']
    exact congrFun MvPowerSeries.subst_self h
  let e : MvPowerSeries (Fin 2) B ≃ₐ[B] MvPowerSeries (Fin 2) B :=
    AlgEquiv.ofAlgHom Sw Sg (AlgHom.ext h2) (AlgHom.ext h1)
  have hψ0 : ∀ i, constantCoeff (X.act a i) = 0 := (X.isLawHom_act a).1
  have hψ0' : ∀ i, constantCoeff (Y.act a i) = 0 := (Y.isLawHom_act a).1

  have himage : (e : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) '' Set.range (Y.act a) =
      Set.range (w.toSeries.comp (X.act a)) := by
    ext y
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    rw [w.isODHom.2.1 a]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, by simp [e, Sw, Series.comp]⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, by simp [e, Sw, Series.comp]⟩
  have hI : Ideal.span (Set.range (X.act a)) =
      (Ideal.span (Set.range (Y.act a))).map (e : MvPowerSeries (Fin 2) B →+* MvPowerSeries (Fin 2) B) := by
    rw [Ideal.map_span, himage]
    apply le_antisymm
    ·
      have hcw : ∀ i, constantCoeff ((w.toSeries.comp (X.act a)) i) = 0 := Series.constantCoeff_comp hw0 hψ0
      have heq : X.act a = g.toSeries.comp (w.toSeries.comp (X.act a)) := by
        rw [← Series.comp_assoc _ _ _ hw0 hψ0, show g.toSeries.comp w.toSeries = (g.comp w).toSeries from rfl, hgw]
        exact (Series.id_comp _ hψ0).symm
      conv_lhs => rw [heq]
      exact span_comp_le _ _ hg0 hcw
    · exact span_comp_le _ _ hw0 hψ0
  exact ⟨Ideal.quotientEquivAlg (Ideal.span (Set.range (Y.act a))) (Ideal.span (Set.range (X.act a))) e hI⟩

theorem natCast_eq_zero_of_hasHeight {k : Type} [Field k] (Y : FormalODModule q k) {h : ℕ} (hh : Y.HasHeight h)
    (h0 : h ≠ 0) : ((q : ℕ) : k) = 0 := by
  by_contra hq
  set ψ : Series k := Y.act (q : Zp2 q) with hψdef
  have hcc : ∀ i, constantCoeff (ψ i) = 0 := (Y.isLawHom_act _).1
  have hlin : MvFormalGroup.linearPart ψ = ((q : ℕ) : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    rw [hψdef, Y.act_natCast q, MvFormalGroup.linearPart_nthSeries, Nat.cast_smul_eq_nsmul]
  let ψ' : Series k := fun i => ((q : ℕ) : k)⁻¹ • ψ i
  have hcc' : ∀ i, constantCoeff (ψ' i) = 0 := fun i => by
    show constantCoeff (((q : ℕ) : k)⁻¹ • ψ i) = 0
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hcc i, mul_zero]
  have hlin' : MvFormalGroup.linearPart ψ' = 1 := by
    ext i j
    have := congrFun (congrFun hlin i) j
    simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
    show coeff (Finsupp.single j 1) (((q : ℕ) : k)⁻¹ • ψ i) = _
    rw [map_smul, this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  obtain ⟨χ, hχ0, hχψ, -⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one ψ' hcc' hlin'
  have hI : Ideal.span (Set.range ψ) = Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k)) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker]
      exact hcc i
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, ← hχψ i]
      refine Ideal.span_le.2 ?_ (subst_mem_span ψ' hcc' (χ i) (hχ0 i))
      rintro _ ⟨i', rfl⟩
      show ((q : ℕ) : k)⁻¹ • ψ i' ∈ Ideal.span (Set.range ψ)
      have hmem : ψ i' ∈ Ideal.span (Set.range ψ) := Ideal.subset_span (Set.mem_range_self i')
      rw [MvPowerSeries.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ hmem

  let cc : MvPowerSeries (Fin 2) k →ₐ[k] k :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) k →+* k) with
      commutes' := fun r => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
          MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.constantCoeff_C] }
  have hccs : Function.Surjective cc := fun r => ⟨MvPowerSeries.C r, MvPowerSeries.constantCoeff_C r⟩
  have hker : Ideal.span (Set.range ψ) = RingHom.ker cc := by
    rw [hI, MvPowerSeries.span_range_X_eq_ker_constantCoeff]; rfl
  have e1 : FormalODModule.KerAlgebra ψ ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k hker).trans (Ideal.quotientKerAlgEquivOfSurjective hccs)
  have hrank := hh.2.2 k (RingHom.id k)
  rw [Series.map_ringHom_id] at hrank
  have h1 : Module.finrank k (FormalODModule.KerAlgebra ψ) = 1 := by
    rw [e1.toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [← hψdef, h1] at hrank
  exact (Nat.one_lt_pow h0 (one_lt_q q)).ne hrank

end KerAlg

section Main

variable {q : ℕ} [Fact q.Prime]

theorem main {k : Type} [Field k] (j₀ : Zp2 q →+* k) (X₀ : SpecialFormalODModule q j₀)
    (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (resA : A →+* k) (hs : Function.Surjective resA) (j : Zp2 q →+* A) (hj : resA.comp j = j₀)
    (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    X.IsSpecial j ∧ X.HasHeight 4 := by
  have hj' : ∀ x, resA (j x) = j₀ x := fun x => by rw [← hj]; rfl

  have hker : RingHom.ker resA = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resA hs)
  obtain ⟨N, hN⟩ : ∃ N, IsLocalRing.maximalIdeal A ^ N = ⊥ := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    exact ⟨n, hn⟩
  have hnil : ∀ x : A, resA x = 0 → IsNilpotent x := fun x hx => by
    refine ⟨N, ?_⟩
    have : x ^ N ∈ IsLocalRing.maximalIdeal A ^ N := Ideal.pow_mem_pow (by rw [← hker]; exact hx) N
    rwa [hN, Ideal.mem_bot] at this

  have hqk : ((q : ℕ) : k) = 0 := natCast_eq_zero_of_hasHeight X₀.toFormalODModule X₀.hasHeight (by norm_num)
  obtain ⟨K, hK⟩ : ∃ K, ((q : ℕ) : A) ^ K = 0 := hnil _ (by rw [map_natCast, hqk])
  have hK1 : ((q : ℕ) : k) ^ 1 = 0 := by rw [pow_one, hqk]

  obtain ⟨ζ, hζ⟩ := exists_isUnit_sub_frobenius q
  let u : Aˣ := (hζ.map j).unit
  have hu : (u : A) = j ζ - j (WittVector.frobenius ζ) := by rw [IsUnit.unit_spec, map_sub]
  let ub : kˣ := Units.map (resA : A →* k) u
  have hub : (ub : k) = j₀ ζ - j₀ (WittVector.frobenius ζ) := by
    show resA (u : A) = _
    rw [hu, map_sub, hj', hj']

  have hZ0 : Module.finrank k ((X.map resA).lieZero j₀) = 1 := by
    obtain ⟨e⟩ := nonempty_eig_equiv w hw (fun a => j₀ a)
    rw [lieZero_eq_eig, e.finrank_eq, ← lieZero_eq_eig]
    haveI := X₀.isSpecial.2.1
    exact Module.Invertible.finrank_eq_one k _
  have hZ1 : Module.finrank k ((X.map resA).lieOne j₀) = 1 := by
    obtain ⟨e⟩ := nonempty_eig_equiv w hw (fun a => j₀ (WittVector.frobenius a))
    rw [lieOne_eq_eig, e.finrank_eq, ← lieOne_eq_eig]
    haveI := X₀.isSpecial.2.2
    exact Module.Invertible.finrank_eq_one k _

  have htrk : (e₀ (X.map resA) j₀ ζ ub).trace = 1 :=
    trace_eq_one_of_finrank _ (e₀_mul_e₀ (X.map resA) j₀ hK1 ζ ub hub)
      (by rw [← lieZero_eq (X.map resA) j₀ hK1 ζ ub hub]; exact hZ0)
      (by rw [← lieOne_eq (X.map resA) j₀ hK1 ζ ub hub]; exact hZ1)

  have hres_tr : resA (e₀ X j ζ u).trace = (e₀ (X.map resA) j₀ ζ ub).trace := by
    rw [trace_e₀, trace_e₀, map_mul, map_sub, map_mul, hj', map_ofNat, trace_lp_map]
    congr 1
  have hν : IsNilpotent ((e₀ X j ζ u).trace - 1) := hnil _ (by rw [map_sub, map_one, hres_tr, htrk, sub_self])
  obtain ⟨htr, hdet⟩ := trace_eq_one_and_det_eq_zero _ (e₀_mul_e₀ X j hK ζ u hu) hν
  obtain ⟨-, hcpl, hi0, hi1⟩ :=
    Matrix.isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero (e₀ X j ζ u) htr hdet
  have hspecial : X.IsSpecial j := by
    refine ⟨?_, ?_, ?_⟩
    · rw [lieZero_eq X j hK ζ u hu, lieOne_eq X j hK ζ u hu]; exact hcpl
    · rw [lieZero_eq X j hK ζ u hu]; exact hi0
    · rw [lieOne_eq X j hK ζ u hu]; exact hi1

  have hψ0 : ∀ i, constantCoeff (X.act (q : Zp2 q) i) = 0 := (X.isLawHom_act _).1

  have hrank0 : Module.finrank k (FormalODModule.KerAlgebra (X₀.act (q : Zp2 q))) = q ^ 4 := by
    have := X₀.hasHeight.2.2 k (RingHom.id k)
    rwa [Series.map_ringHom_id] at this
  have hrankb : Module.finrank k (FormalODModule.KerAlgebra ((X.map resA).act (q : Zp2 q))) = q ^ 4 := by
    obtain ⟨e⟩ := nonempty_kerAlgebra_equiv (X.map resA) X₀.toFormalODModule w hw (q : Zp2 q)
    rw [← e.toLinearEquiv.finrank_eq, hrank0]
  have hfin : Module.Finite k (MvPowerSeries (Fin 2) k ⧸
      Ideal.span (Set.range fun i => MvPowerSeries.map resA (X.act (q : Zp2 q) i))) := by
    have hpos : 0 < Module.finrank k (FormalODModule.KerAlgebra ((X.map resA).act (q : Zp2 q))) := by
      rw [hrankb]; exact pow_pos (Fact.out : q.Prime).pos 4
    exact Module.finite_of_finrank_pos hpos
  obtain ⟨hF, hFr, -⟩ :=
    MvPowerSeries.finite_free_finrank_quotient_span_eq_of_isArtinianRing_of_finite_map resA hs
      (X.act (q : Zp2 q)) hψ0 hfin
  have hproj : Module.Projective A (FormalODModule.KerAlgebra (X.act (q : Zp2 q))) :=
    Module.Projective.of_free
  have hheight : X.HasHeight 4 := by
    refine ⟨hF, hproj, ?_⟩
    intro κ _ f

    have hkf : RingHom.ker resA ≤ RingHom.ker f := fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      exact ((hnil x hx).map f).eq_zero
    let g : k →+* κ := resA.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨f, hkf⟩
    have hgf : g.comp resA = f := RingHom.liftOfRightInverse_comp _ _ _ _
    have hmap : (X.act (q : Zp2 q)).map f = (((X.map resA).map g).act (q : Zp2 q)) := by
      rw [FormalODModule.map_act, FormalODModule.map_act, Series.map_map, hgf]
    rw [hmap]
    obtain ⟨e⟩ := nonempty_kerAlgebra_equiv ((X.map resA).map g) (X₀.toFormalODModule.map g) (w.map g)
      (isIso_map w hw g) (q : Zp2 q)
    rw [← e.toLinearEquiv.finrank_eq]
    exact X₀.hasHeight.2.2 κ g
  exact ⟨hspecial, hheight⟩

end Main

end R4AutoSH

end

theorem solution
    {q : ℕ} [Fact q.Prime]
    (O : Type) [CommRing O] [IsLocalRing O]
    (ι : CerednikDrinfeld.Zp2 q →+* O)
    (X₀ : CerednikDrinfeld.SpecialFormalODModule q ((IsLocalRing.residue O).comp ι))
    (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* IsLocalRing.ResidueField O) (hs : Function.Surjective resA)
    (hc : resA.comp (algebraMap O A) = IsLocalRing.residue O)
    (X : CerednikDrinfeld.FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    X.IsSpecial ((algebraMap O A).comp ι) ∧ X.HasHeight 4 :=
  R4AutoSH.main ((IsLocalRing.residue O).comp ι) X₀ A resA hs ((algebraMap O A).comp ι)
    (by rw [← RingHom.comp_assoc, hc]) X w hw

end S_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing (solution)
