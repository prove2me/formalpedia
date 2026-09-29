-- Prove2me | solution 1 for Derivation.add_mulLeft_pow_char
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8b9698c1-69f0-5b26-853a-813f44d953bf

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Module.NatInt
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Derivation_add_mulLeft_pow_char

set_option autoImplicit false
set_option maxSynthPendingDepth 3
universe u v

namespace Star2B

variable {R : Type u} {F : Type v} [CommRing R] [CommRing F] [Algebra R F]

private def sseq (d : Derivation R F F) (a : F) : ℕ → F
  | 0 => 1
  | m + 1 => d (sseq d a m) + a * sseq d a m

private lemma sseq_zero (d : Derivation R F F) (a : F) : sseq d a 0 = 1 := rfl

private lemma sseq_succ (d : Derivation R F F) (a : F) (m : ℕ) :
    sseq d a (m + 1) = d (sseq d a m) + a * sseq d a m := rfl

private lemma mul_app (f g : F →ₗ[R] F) (x : F) : (f * g) x = f (g x) := rfl

private lemma mulLeft_app (a x : F) : LinearMap.mulLeft R a x = a * x := rfl

private lemma dtl_app (d : Derivation R F F) (x : F) : d.toLinearMap x = d x := rfl

private lemma key (d : Derivation R F F) (a s : F) (i : ℕ) :
    (d.toLinearMap + LinearMap.mulLeft R a) * (LinearMap.mulLeft R s * d.toLinearMap ^ i)
      = LinearMap.mulLeft R s * d.toLinearMap ^ (i + 1)
        + LinearMap.mulLeft R (d s + a * s) * d.toLinearMap ^ i := by
  ext f
  simp only [mul_app, LinearMap.add_apply, mulLeft_app, dtl_app, pow_succ',
    Derivation.leibniz, smul_eq_mul]
  ring

private lemma struct (d : Derivation R F F) (a : F) (n : ℕ) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ n
      = ∑ i ∈ Finset.range (n + 1),
          n.choose i • (LinearMap.mulLeft R (sseq d a (n - i)) * d.toLinearMap ^ i) := by
  induction n with
  | zero =>
      simp [sseq_zero, LinearMap.mulLeft_one, ← Module.End.one_eq_id, mul_one, one_mul]
  | succ n ih =>
      have hterm : ∀ i ∈ Finset.range (n + 1),
          (d.toLinearMap + LinearMap.mulLeft R a)
              * (n.choose i • (LinearMap.mulLeft R (sseq d a (n - i)) * d.toLinearMap ^ i))
            = n.choose i • (LinearMap.mulLeft R (sseq d a (n - i)) * d.toLinearMap ^ (i + 1))
              + n.choose i • (LinearMap.mulLeft R (sseq d a (n + 1 - i)) * d.toLinearMap ^ i) := by
        intro i hi
        have hle : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_smul_comm, key, smul_add, show n + 1 - i = n - i + 1 by omega, sseq_succ]
      have hL : (∑ i ∈ Finset.range (n + 1),
            n.choose i • (LinearMap.mulLeft R (sseq d a (n + 1 - i)) * d.toLinearMap ^ i))
          = (∑ i ∈ Finset.range (n + 1),
              n.choose (i + 1) • (LinearMap.mulLeft R (sseq d a (n - i)) * d.toLinearMap ^ (i + 1)))
            + LinearMap.mulLeft R (sseq d a (n + 1)) := by
        rw [Finset.sum_range_succ']
        conv_rhs => rw [Finset.sum_range_succ]
        simp [Nat.succ_sub_succ, Nat.choose_succ_self, Nat.choose_zero_right]
      have hR : (∑ j ∈ Finset.range (n + 1 + 1),
            (n + 1).choose j • (LinearMap.mulLeft R (sseq d a (n + 1 - j)) * d.toLinearMap ^ j))
          = ((∑ i ∈ Finset.range (n + 1),
                n.choose i • (LinearMap.mulLeft R (sseq d a (n - i)) * d.toLinearMap ^ (i + 1)))
              + (∑ i ∈ Finset.range (n + 1),
                n.choose (i + 1) • (LinearMap.mulLeft R (sseq d a (n - i)) * d.toLinearMap ^ (i + 1))))
            + LinearMap.mulLeft R (sseq d a (n + 1)) := by
        rw [Finset.sum_range_succ']
        congr 1
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Nat.choose_succ_succ', add_smul, Nat.succ_sub_succ]
        · simp [Nat.choose_zero_right, pow_zero, mul_one]
      rw [pow_succ', ih, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        hL, hR]
      abel

private lemma char_nsmul_zero (p : ℕ) [CharP F p] (x : F →ₗ[R] F) : p • x = 0 := by
  ext f
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

private theorem iterate_form (p : ℕ) [Fact p.Prime] [CharP F p] (d : Derivation R F F) (a : F) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ p
      = d.toLinearMap ^ p + LinearMap.mulLeft R (sseq d a p) := by
  have hp : p.Prime := Fact.out
  rw [struct, Finset.sum_range_succ,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hp.pos)
      (fun i hi hne => by
        obtain ⟨c, hc⟩ := hp.dvd_choose_self hne (Finset.mem_range.mp hi)
        rw [hc, mul_smul, char_nsmul_zero])]
  simp [Nat.choose_zero_right, Nat.choose_self, sseq_zero,
    LinearMap.mulLeft_one, ← Module.End.one_eq_id, mul_one, one_mul]
  abel

private theorem head_b_of_collapse (p : ℕ) [Fact p.Prime] [CharP F p] (d : Derivation R F F) (a : F)
    (hcollapse : sseq d a p = a ^ p + (d.toLinearMap ^ (p - 1)) a) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ p
      = d.toLinearMap ^ p + LinearMap.mulLeft R (a ^ p + (d.toLinearMap ^ (p - 1)) a) := by
  rw [iterate_form, hcollapse]

example (d : Derivation R F F) (a : F) : sseq d a 2 = a ^ 2 + d a := by
  simp [sseq, Derivation.map_one_eq_zero, sq]
  ring

section layer2

open Polynomial

private lemma mul_app2 (f g : F →ₗ[R] F) (x : F) : (f * g) x = f (g x) := rfl

private lemma mulLeft_app2 (a x : F) : LinearMap.mulLeft R a x = a * x := rfl

private lemma dtl_app2 (d : Derivation R F F) (x : F) : d.toLinearMap x = d x := rfl

private lemma mulLeft_mul2 (a b : F) :
    LinearMap.mulLeft R a * LinearMap.mulLeft R b = LinearMap.mulLeft R (a * b) := by
  ext x; simp

private lemma dm_rel2 (d : Derivation R F F) (b : F) :
    d.toLinearMap * LinearMap.mulLeft R b
      = LinearMap.mulLeft R b * d.toLinearMap + LinearMap.mulLeft R (d b) := by
  ext f
  simp only [mul_app2, LinearMap.add_apply, mulLeft_app2, dtl_app2, Derivation.leibniz,
    smul_eq_mul]
  ring

private lemma mulLeft_pow' (a : F) (n : ℕ) :
    (LinearMap.mulLeft R a) ^ n = LinearMap.mulLeft R (a ^ n) := by
  induction n with
  | zero => simp [LinearMap.mulLeft_one, ← Module.End.one_eq_id]
  | succ n ih => rw [pow_succ, ih, mulLeft_mul2, ← pow_succ]

private noncomputable def zpoly (d : Derivation R F F) (a : F) :
    Polynomial (F →ₗ[R] F) :=
  C d.toLinearMap + C (LinearMap.mulLeft R a) * X

private lemma deriv_pow_noncomm {A : Type*} [Ring A] (z : Polynomial A) (n : ℕ) :
    derivative (z ^ n)
      = ∑ i ∈ Finset.range n, z ^ i * derivative z * z ^ (n - 1 - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, derivative_mul, ih, Finset.sum_mul, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hidx : n - 1 - i + 1 = n - i := by
          have := Finset.mem_range.mp hi; omega
        rw [mul_assoc (z ^ i * derivative z) (z ^ (n - 1 - i)) z, ← pow_succ, hidx]
      · rw [Nat.sub_self, pow_zero, mul_one]

private lemma deriv_zpoly (d : Derivation R F F) (a : F) :
    derivative (zpoly d a) = C (LinearMap.mulLeft R a) := by
  rw [zpoly, derivative_add, derivative_C, derivative_mul, derivative_C, derivative_X]
  simp

private noncomputable def adSeq (z w : Polynomial (F →ₗ[R] F)) : ℕ → Polynomial (F →ₗ[R] F)
  | 0 => w
  | n + 1 => z * adSeq z w n - adSeq z w n * z

private lemma adSeq_zero (z w : Polynomial (F →ₗ[R] F)) : adSeq z w 0 = w := rfl

private lemma adSeq_succ (z w : Polynomial (F →ₗ[R] F)) (n : ℕ) :
    adSeq z w (n + 1) = z * adSeq z w n - adSeq z w n * z := rfl

private lemma ad_step (d : Derivation R F F) (a c : F) :
    zpoly d a * C (LinearMap.mulLeft R c) - C (LinearMap.mulLeft R c) * zpoly d a
      = C (LinearMap.mulLeft R (d c)) := by
  have hdm : d.toLinearMap * LinearMap.mulLeft R c
      - LinearMap.mulLeft R c * d.toLinearMap = LinearMap.mulLeft R (d c) := by
    rw [dm_rel2]; abel
  have hcomm : LinearMap.mulLeft R a * LinearMap.mulLeft R c
      = LinearMap.mulLeft R c * LinearMap.mulLeft R a := by
    rw [mulLeft_mul2, mulLeft_mul2, mul_comm]
  have hXC : (X : Polynomial (F →ₗ[R] F)) * C (LinearMap.mulLeft R c)
      = C (LinearMap.mulLeft R c) * X := X_mul_C _
  have hCC : C (LinearMap.mulLeft R a) * C (LinearMap.mulLeft R c)
      = C (LinearMap.mulLeft R c) * C (LinearMap.mulLeft R a) := by
    rw [← C_mul, ← C_mul, hcomm]
  have hrhs : (C (LinearMap.mulLeft R (d c)) : Polynomial (F →ₗ[R] F))
      = C d.toLinearMap * C (LinearMap.mulLeft R c)
        - C (LinearMap.mulLeft R c) * C d.toLinearMap := by
    rw [← hdm, C_sub, C_mul, C_mul]
  rw [zpoly, hrhs, add_mul, mul_add,
    mul_assoc (C (LinearMap.mulLeft R a)) X (C (LinearMap.mulLeft R c)), hXC,
    ← mul_assoc (C (LinearMap.mulLeft R a)) (C (LinearMap.mulLeft R c)) X, hCC,
    mul_assoc (C (LinearMap.mulLeft R c)) (C (LinearMap.mulLeft R a)) X]
  abel

private lemma adSeq_deg (d : Derivation R F F) (a b : F) (k : ℕ) :
    adSeq (zpoly d a) (C (LinearMap.mulLeft R b)) k
      = C (LinearMap.mulLeft R ((d.toLinearMap ^ k) b)) := by
  induction k with
  | zero => rw [adSeq_zero, pow_zero]; rfl
  | succ k ih =>
      rw [adSeq_succ, ih, ad_step]
      congr 2
      rw [pow_succ', mul_app2]
      rfl

private lemma adSeq_expand (z w : Polynomial (F →ₗ[R] F)) (n : ℕ) :
    adSeq z w n
      = ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ i * (n.choose i : ℤ)) • (z ^ (n - i) * w * z ^ i) := by
  induction n with
  | zero => simp [adSeq_zero]
  | succ n ih =>
      rw [adSeq_succ, ih, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun i hi => show
          z * (((-1:ℤ)^i * (n.choose i : ℤ)) • (z ^ (n - i) * w * z ^ i))
            = ((-1:ℤ)^i * (n.choose i : ℤ)) • (z ^ (n + 1 - i) * w * z ^ i) from by
        rw [mul_smul_comm]
        congr 1
        rw [← mul_assoc, ← mul_assoc, ← pow_succ',
          show n - i + 1 = n + 1 - i from by have := Finset.mem_range.mp hi; omega])]
      rw [Finset.sum_congr rfl (fun i _ => show
          (((-1:ℤ)^i * (n.choose i : ℤ)) • (z ^ (n - i) * w * z ^ i)) * z
            = ((-1:ℤ)^i * (n.choose i : ℤ)) • (z ^ (n - i) * w * z ^ (i + 1)) from by
        rw [smul_mul_assoc]
        congr 1
        rw [mul_assoc, ← pow_succ])]
      conv_rhs => rw [Finset.sum_range_succ']
      conv_lhs => rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ, Nat.sub_zero, pow_zero, mul_one, Nat.choose_zero_right,
        Nat.cast_one, one_smul]
      have hext : (∑ i ∈ Finset.range n,
            ((-1:ℤ)^(i+1) * (n.choose (i+1) : ℤ)) • (z ^ (n - i) * w * z ^ (i+1)))
          = ∑ i ∈ Finset.range (n+1),
            ((-1:ℤ)^(i+1) * (n.choose (i+1) : ℤ)) • (z ^ (n - i) * w * z ^ (i+1)) := by
        rw [Finset.sum_range_succ]
        simp [Nat.choose_succ_self]
      rw [hext]
      have hpascal : ∀ i : ℕ, ((-1:ℤ)^(i+1) * (((n+1).choose (i+1)) : ℤ))
          = ((-1:ℤ)^(i+1) * ((n.choose (i+1)) : ℤ)) - ((-1:ℤ)^i * ((n.choose i) : ℤ)) := by
        intro i
        rw [Nat.choose_succ_succ' n i]
        push_cast
        ring
      have hrw : (∑ i ∈ Finset.range (n+1),
            ((-1:ℤ)^(i+1) * (((n+1).choose (i+1)) : ℤ)) • (z ^ (n - i) * w * z ^ (i+1)))
          = (∑ i ∈ Finset.range (n+1),
              ((-1:ℤ)^(i+1) * ((n.choose (i+1)) : ℤ)) • (z ^ (n - i) * w * z ^ (i+1)))
            - ∑ i ∈ Finset.range (n+1),
              ((-1:ℤ)^i * ((n.choose i) : ℤ)) • (z ^ (n - i) * w * z ^ (i+1)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [hpascal i, sub_smul])
      rw [hrw]
      abel

private lemma signed_choose_int (p : ℕ) (hp : p.Prime) :
    ∀ i, i ≤ p - 1 → (p : ℤ) ∣ ((-1 : ℤ) ^ i * (((p-1).choose i) : ℤ) - 1) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
      intro hi1
      have hi : i ≤ p - 1 := by omega
      have hpas : (p-1).choose i + (p-1).choose (i+1) = p.choose (i+1) := by
        conv_rhs => rw [← Nat.succ_pred_eq_of_pos hp.pos]
        exact (Nat.choose_succ_succ' (p-1) i).symm
      have hdvd : (p : ℤ) ∣ (p.choose (i+1) : ℤ) := by
        exact_mod_cast Int.natCast_dvd_natCast.mpr
          (hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega))
      have hsplit : (-1:ℤ)^(i+1) * (((p-1).choose (i+1)) : ℤ) - 1
          = (-1:ℤ)^(i+1) * ((p.choose (i+1)) : ℤ)
            + ((-1:ℤ)^i * (((p-1).choose i) : ℤ) - 1) := by
        rw [show ((p-1).choose (i+1) : ℤ) = (p.choose (i+1) : ℤ) - ((p-1).choose i : ℤ) from by
          rw [← hpas]; push_cast; ring]
        ring
      rw [hsplit]
      exact dvd_add (Dvd.dvd.mul_left hdvd _) (ih hi)

private lemma mulLeft_add2 (a b : F) :
    LinearMap.mulLeft R (a + b) = LinearMap.mulLeft R a + LinearMap.mulLeft R b := by
  ext x; simp [add_mul]

private lemma z_natDegree_le (d : Derivation R F F) (a : F) : (zpoly d a).natDegree ≤ 1 := by
  rw [zpoly]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · simp [Polynomial.natDegree_C]
  · exact le_trans Polynomial.natDegree_mul_le
      (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X_le])

private lemma W_pow_natDegree_le (d : Derivation R F F) (a : F) (n : ℕ) :
    ((zpoly d a) ^ n).natDegree ≤ n :=
  le_trans Polynomial.natDegree_pow_le
    (le_trans (Nat.mul_le_mul_left n (z_natDegree_le d a)) (le_of_eq (mul_one n)))

private lemma W_coeff_top (d : Derivation R F F) (a : F) (n : ℕ) :
    ((zpoly d a) ^ n).coeff n = (LinearMap.mulLeft R a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hz : ((zpoly d a) ^ n).coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (Nat.lt_succ_of_le (W_pow_natDegree_le d a n))
      have hsplit : ∀ q : Polynomial (F →ₗ[R] F), (zpoly d a * q).coeff (n + 1)
          = d.toLinearMap * q.coeff (n + 1) + LinearMap.mulLeft R a * q.coeff n := by
        intro q
        rw [zpoly, add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
      rw [pow_succ', hsplit, ih, hz, mul_zero, zero_add, ← pow_succ']

private lemma W_coeff_zero' (d : Derivation R F F) (a : F) (n : ℕ) :
    ((zpoly d a) ^ n).coeff 0 = d.toLinearMap ^ n := by
  have h0 : (zpoly d a).coeff 0 = d.toLinearMap := by
    rw [zpoly, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
      mul_zero, add_zero, Polynomial.coeff_C_zero]
  rw [← Polynomial.constantCoeff_apply, map_pow, Polynomial.constantCoeff_apply, h0]

section primepart
variable (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] in
private lemma char_nsmul2 (f : F →ₗ[R] F) : p • f = 0 := by
  ext v
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

omit [Fact p.Prime] in
private lemma charP_nsmul_P (x : Polynomial (F →ₗ[R] F)) : p • x = 0 := by
  ext n
  rw [Polynomial.coeff_smul, Polynomial.coeff_zero, char_nsmul2 p]

omit [Fact p.Prime] in
private lemma zsmul_eq_self_of_dvd (c : ℤ) (hdvd : (p:ℤ) ∣ (c - 1))
    (x : Polynomial (F →ₗ[R] F)) : c • x = x := by
  obtain ⟨m, hm⟩ := hdvd
  have hc : c = 1 + (p:ℤ) * m := by omega
  rw [hc, add_zsmul, one_zsmul, mul_zsmul, natCast_zsmul, charP_nsmul_P p, add_zero]

private lemma nsmul_cancelA (k : ℕ) (hk : ¬ (p ∣ k)) (x : F →ₗ[R] F) (hx : k • x = 0) :
    x = 0 := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime k p := (hp.coprime_iff_not_dvd.mpr hk).symm
  have hbez : (1 : ℤ) = k * Nat.gcdA k p + p * Nat.gcdB k p := by
    have hg := Nat.gcd_eq_gcd_ab k p
    rw [show Nat.gcd k p = 1 from hcop] at hg
    exact_mod_cast hg
  calc x = (1:ℤ) • x := (one_zsmul x).symm
    _ = ((k : ℤ) * Nat.gcdA k p + (p:ℤ) * Nat.gcdB k p) • x := by rw [← hbez]
    _ = (Nat.gcdA k p * (k:ℤ)) • x + (Nat.gcdB k p * (p:ℤ)) • x := by
        rw [add_zsmul, mul_comm ((k:ℤ)) _, mul_comm ((p:ℤ)) _]
    _ = Nat.gcdA k p • ((k:ℤ) • x) + Nat.gcdB k p • ((p:ℤ) • x) := by
        rw [mul_smul, mul_smul]
    _ = 0 := by
        rw [natCast_zsmul, natCast_zsmul, hx, char_nsmul2 p, smul_zero, smul_zero, add_zero]

private lemma adSeq_expand_prime (z w : Polynomial (F →ₗ[R] F)) :
    adSeq z w (p - 1) = ∑ i ∈ Finset.range p, z ^ (p - 1 - i) * w * z ^ i := by
  have hp : p.Prime := Fact.out
  have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
  rw [adSeq_expand, hp1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : i ≤ p - 1 := by have := Finset.mem_range.mp hi; omega
  exact zsmul_eq_self_of_dvd p _ (signed_choose_int p hp i hle) _

private lemma deriv_W (d : Derivation R F F) (a : F) :
    derivative ((zpoly d a) ^ p)
      = C (LinearMap.mulLeft R ((d.toLinearMap ^ (p - 1)) a)) := by
  rw [deriv_pow_noncomm, deriv_zpoly]
  have hreflect : (∑ i ∈ Finset.range p,
        (zpoly d a) ^ (p - 1 - i) * C (LinearMap.mulLeft R a) * (zpoly d a) ^ i)
      = ∑ i ∈ Finset.range p,
        (zpoly d a) ^ i * C (LinearMap.mulLeft R a) * (zpoly d a) ^ (p - 1 - i) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < p := Finset.mem_range.mp hj
    have he : p - 1 - (p - 1 - j) = j := by omega
    rw [he]
  rw [← hreflect, ← adSeq_expand_prime p (zpoly d a) (C (LinearMap.mulLeft R a)), adSeq_deg]

private lemma W_coeff_succ (d : Derivation R F F) (a : F) (n : ℕ) :
    ((zpoly d a) ^ p).coeff (n + 1) * ((n : F →ₗ[R] F) + 1)
      = (C (LinearMap.mulLeft R ((d.toLinearMap ^ (p - 1)) a))).coeff n := by
  rw [← Polynomial.coeff_derivative, deriv_W p]

private lemma W_coeff_one (d : Derivation R F F) (a : F) :
    ((zpoly d a) ^ p).coeff 1 = LinearMap.mulLeft R ((d.toLinearMap ^ (p - 1)) a) := by
  have h := W_coeff_succ p d a 0
  simpa using h

private lemma W_coeff_mid (d : Derivation R F F) (a : F) (n : ℕ)
    (h1 : 1 ≤ n) (h2 : n + 1 ≤ p - 1) : ((zpoly d a) ^ p).coeff (n + 1) = 0 := by
  have hp : p.Prime := Fact.out
  have h2le := hp.two_le
  have hW := W_coeff_succ p d a n
  rw [Polynomial.coeff_C, if_neg (by omega : ¬ n = 0)] at hW
  have hcast : ((n : F →ₗ[R] F) + 1) = ((n + 1 : ℕ) : F →ₗ[R] F) := by push_cast; ring
  rw [hcast] at hW
  apply nsmul_cancelA p (n + 1) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  rw [nsmul_eq_mul, (Nat.cast_commute (n + 1) (((zpoly d a) ^ p).coeff (n + 1))).eq]
  exact hW

private noncomputable def evalOne : Polynomial (F →ₗ[R] F) →+* (F →ₗ[R] F) :=
  Polynomial.eval₂RingHom' (RingHom.id _) 1 (fun a => Commute.one_right a)

private lemma evalOne_apply (q : Polynomial (F →ₗ[R] F)) :
    evalOne (R := R) (F := F) q = Polynomial.eval₂ (RingHom.id _) 1 q := rfl

private lemma evalOne_z (d : Derivation R F F) (a : F) :
    evalOne (zpoly d a) = d.toLinearMap + LinearMap.mulLeft R a := by
  rw [zpoly, map_add, map_mul, evalOne_apply, evalOne_apply, evalOne_apply,
    Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X]
  simp

private lemma evalOne_W_sum (d : Derivation R F F) (a : F) :
    evalOne ((zpoly d a) ^ p)
      = d.toLinearMap ^ p + (LinearMap.mulLeft R a) ^ p
        + LinearMap.mulLeft R ((d.toLinearMap ^ (p - 1)) a) := by
  have hp : p.Prime := Fact.out
  have h2le := hp.two_le
  have hdeg : ((zpoly d a) ^ p).natDegree < p + 1 :=
    Nat.lt_succ_of_le (W_pow_natDegree_le d a p)
  rw [evalOne_apply, Polynomial.eval₂_eq_sum_range' (RingHom.id _) hdeg 1]
  simp only [RingHom.id_apply, one_pow, mul_one]
  rw [Finset.sum_range_succ']
  have hsplit2 : (∑ i ∈ Finset.range p, ((zpoly d a) ^ p).coeff (i + 1))
      = (∑ i ∈ Finset.range (p - 1), ((zpoly d a) ^ p).coeff (i + 1 + 1))
        + ((zpoly d a) ^ p).coeff (0 + 1) := by
    conv_lhs => rw [show Finset.range p = Finset.range ((p - 1) + 1) from by
      congr 1
      have := hp.pos
      omega]
    rw [Finset.sum_range_succ']
  rw [hsplit2]
  have htail : (∑ i ∈ Finset.range (p - 1), ((zpoly d a) ^ p).coeff (i + 1 + 1))
      = (LinearMap.mulLeft R a) ^ p := by
    rw [Finset.sum_eq_single (p - 2)]
    · rw [show p - 2 + 1 + 1 = p from by omega]
      exact W_coeff_top d a p
    · intro i hi hne
      have hilt : i < p - 1 := Finset.mem_range.mp hi
      have hine : i ≠ p - 2 := hne
      exact W_coeff_mid p d a (i + 1) (by omega) (by omega)
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega : p - 2 < p - 1)) h
  rw [htail, W_coeff_one p d a, W_coeff_zero' d a p]
  abel

private theorem hochschild_full (d : Derivation R F F) (a : F) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ p
      = d.toLinearMap ^ p + LinearMap.mulLeft R (a ^ p + (d.toLinearMap ^ (p - 1)) a) := by
  have h1 : evalOne ((zpoly d a) ^ p) = (d.toLinearMap + LinearMap.mulLeft R a) ^ p := by
    rw [map_pow, evalOne_z]
  have h2 := evalOne_W_sum p d a
  rw [h1] at h2
  rw [h2, mulLeft_add2, ← mulLeft_pow']
  abel

end primepart

end layer2

end Star2B

theorem solution {R : Type u} {F : Type v} [CommRing R] [CommRing F]
    [Algebra R F] (p : ℕ) [Fact p.Prime] [CharP F p] (d : Derivation R F F) (a : F) :
    (d.toLinearMap + LinearMap.mulLeft R a) ^ p
      = d.toLinearMap ^ p + LinearMap.mulLeft R (a ^ p + (d.toLinearMap ^ (p - 1)) a) :=
  Star2B.hochschild_full p d a

end S_Derivation_add_mulLeft_pow_char
end P2MW
export P2MW.S_Derivation_add_mulLeft_pow_char (solution)
