-- Prove2me | solution 1 for Erdos393Proof.core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:45:39.892179+00:00
-- url     : https://prove2.me/submissions/cdc926a2-64a6-4b75-a222-9d95ce7a8820

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
public import Theorems.Thm_Erdos393Proof_radical_le_self
public import Theorems.Thm_Erdos393Proof_radical_le_of_dvd
public import Theorems.Thm_Erdos393Proof_radical_mul_le
public import Theorems.Thm_Erdos393Proof_radical_pow
public import Theorems.Thm_Erdos393Proof_radical_factorial_le
public import Theorems.Thm_Erdos393Proof_gcd_pow_dvd
public import Theorems.Thm_Erdos393Proof_natAbs_eval_le
public import Theorems.Thm_Erdos393Proof_abc_dichotomy

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (habc : AbcHyp)
    (d k : ℕ) (R : ℤ[X]) (hR0 : R.eval 0 ≠ 0) (hdeg : k + R.natDegree + 2 ≤ d) :
    ∃ K X : ℕ, ∀ y n : ℕ, 1 ≤ y → n ! ≤ y ^ d →
      (y : ℤ) ^ d + (y : ℤ) ^ k * R.eval (y : ℤ) = (d : ℤ) ^ d * n ! → n ! ≤ K * X ^ n := by
  set j := d - k with hj
  have hkj : k + j = d := by omega
  have hd0 : d ≠ 0 := by omega
  set G0 := (R.eval 0).natAbs with hG0def
  have hG0 : 0 < G0 := Int.natAbs_pos.2 hR0
  set CR := ∑ i ∈ Finset.range (R.natDegree + 1), (R.coeff i).natAbs with hCR
  set ε : ℝ := 1 / (2 * d) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨cmax, hcmax⟩ := abc_dichotomy habc ε hε
  set G := G0 ^ d with hGdef
  set K3 := G ^ (2 * d) * (CR * d) ^ (2 * d + 1) with hK3
  refine ⟨G0 ^ d + (G * cmax) ^ d + K3, 4 ^ (2 * d + 1), ?_⟩
  intro y n hy hyd hid
  have hXn : 0 < (4 ^ (2 * d + 1)) ^ n := by positivity
  suffices h : n ! ≤ G0 ^ d ∨ n ! ≤ (G * cmax) ^ d ∨ n ! ≤ K3 * (4 ^ (2 * d + 1)) ^ n by
    rcases h with h | h | h
    · exact h.trans (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
        (Nat.le_mul_of_pos_right _ hXn))
    · exact h.trans (((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans
        (Nat.le_mul_of_pos_right _ hXn))
    · exact h.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  have hy0 : y ≠ 0 := by omega
  have hfac : (y : ℤ) ^ k * ((y : ℤ) ^ j + R.eval (y : ℤ)) = (d : ℤ) ^ d * n ! := by
    rw [← hid, mul_add, ← pow_add, hkj]
  have hsub : (y : ℤ) ∣ R.eval (y : ℤ) - R.eval 0 := by
    have h := sub_dvd_eval_sub (y : ℤ) 0 R
    rwa [sub_zero] at h
  by_cases hRy : R.eval (y : ℤ) = 0
  · -- Then `y ∣ R(0)`, so `y` is bounded.
    left
    rw [hRy, zero_sub, dvd_neg] at hsub
    exact hyd.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hG0 (Int.natCast_dvd.1 hsub)) d)
  right
  set N : ℤ := (y : ℤ) ^ j + R.eval (y : ℤ) with hNdef
  have hNpos : 0 < N := by
    have hpos : (0 : ℤ) < (d : ℤ) ^ d * n ! := by
      have : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
      positivity
    rw [← hfac] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)
  set A0 := y ^ j with hA0def
  set B0 := (R.eval (y : ℤ)).natAbs with hB0def
  set N0 := N.natAbs with hN0def
  have hA0 : 0 < A0 := by positivity
  have hB0 : 0 < B0 := Int.natAbs_pos.2 hRy
  have hN0pos : 0 < N0 := Int.natAbs_pos.2 hNpos.ne'
  have hN0 : (N0 : ℤ) = N := Int.natAbs_of_nonneg hNpos.le
  -- `N` divides `d^d n!`.
  have hN0dvd : N0 ∣ d ^ d * n ! := by
    have h := congrArg Int.natAbs hfac
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at h
    simp only [Int.natAbs_natCast] at h
    exact Dvd.intro_left _ h
  -- The common factor `g` of `y^j` and `R(y)` is bounded.
  set g := Nat.gcd A0 B0 with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hA0
  have hgG : g ≤ G := by
    have hh : 0 < Nat.gcd B0 y := Nat.gcd_pos_of_pos_left _ hB0
    have hgh : g ∣ Nat.gcd B0 y ^ j := by rw [hgdef, Nat.gcd_comm]; exact gcd_pow_dvd y B0 j
    have hhG : Nat.gcd B0 y ∣ G0 := by
      have h1 : ((Nat.gcd B0 y : ℕ) : ℤ) ∣ (y : ℤ) :=
        Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)
      have h2 : ((Nat.gcd B0 y : ℕ) : ℤ) ∣ R.eval (y : ℤ) :=
        Int.natCast_dvd.2 (Nat.gcd_dvd_left _ _)
      have h3 := dvd_sub h2 (h1.trans hsub)
      rw [sub_sub_cancel] at h3
      exact Int.natCast_dvd.1 h3
    calc g ≤ Nat.gcd B0 y ^ j := Nat.le_of_dvd (pow_pos hh j) hgh
      _ ≤ G0 ^ j := Nat.pow_le_pow_left (Nat.le_of_dvd hG0 hhG) j
      _ ≤ G0 ^ d := Nat.pow_le_pow_right hG0 (by omega)
  have hdvdA : g ∣ A0 := Nat.gcd_dvd_left _ _
  have hdvdB : g ∣ B0 := Nat.gcd_dvd_right _ _
  have hdvdN : g ∣ N0 := by
    have h1 : (g : ℤ) ∣ (y : ℤ) ^ j := by exact_mod_cast hdvdA
    have h2 : (g : ℤ) ∣ R.eval (y : ℤ) := Int.natCast_dvd.2 hdvdB
    exact Int.natCast_dvd.1 (dvd_add h1 h2)
  set a1 := A0 / g with ha1def
  set b1 := B0 / g with hb1def
  set c1 := N0 / g with hc1def
  have hcop : Nat.Coprime a1 b1 := Nat.coprime_div_gcd_div_gcd hg
  have ha1 : a1 * g = A0 := Nat.div_mul_cancel hdvdA
  have hb1 : b1 * g = B0 := Nat.div_mul_cancel hdvdB
  have hc1 : c1 * g = N0 := Nat.div_mul_cancel hdvdN
  have ha1pos : 0 < a1 := Nat.div_pos (Nat.le_of_dvd hA0 hdvdA) hg
  have hb1pos : 0 < b1 := Nat.div_pos (Nat.le_of_dvd hB0 hdvdB) hg
  have hc1pos : 0 < c1 := Nat.div_pos (Nat.le_of_dvd hN0pos hdvdN) hg
  -- Apply abc to `a1 + b1 = c1` or `c1 + b1 = a1`, depending on the sign of `R(y)`.
  obtain ⟨W, haW, hWd⟩ : ∃ W : ℕ, a1 ≤ W ∧
      (W ≤ cmax ∨ (W : ℝ) ≤ (radical (a1 * b1 * c1) : ℝ) ^ (1 + ε)) := by
    rcases lt_or_gt_of_ne hRy with hneg | hpos
    · have hB0' : (B0 : ℤ) = -R.eval (y : ℤ) := Int.ofNat_natAbs_of_nonpos hneg.le
      have hrel : N0 + B0 = A0 := by
        have : (N0 : ℤ) + B0 = A0 := by rw [hN0, hB0', hNdef, hA0def]; push_cast; ring
        exact_mod_cast this
      have hsum : c1 + b1 = a1 :=
        Nat.eq_of_mul_eq_mul_right hg (by rw [add_mul, hc1, hb1, ha1, hrel])
      have hcop' : Nat.Coprime c1 b1 := by
        have h := hcop
        rw [← hsum] at h
        exact Nat.coprime_add_self_left.1 h
      refine ⟨a1, le_rfl, ?_⟩
      rcases hcmax c1 b1 a1 hc1pos hb1pos hcop' hsum with h | h
      · exact Or.inl h
      · right
        rwa [show c1 * b1 * a1 = a1 * b1 * c1 by ring] at h
    · have hB0' : (B0 : ℤ) = R.eval (y : ℤ) := Int.natAbs_of_nonneg hpos.le
      have hrel : A0 + B0 = N0 := by
        have : (A0 : ℤ) + B0 = N0 := by rw [hN0, hB0', hNdef, hA0def]; push_cast; ring
        exact_mod_cast this
      have hsum : a1 + b1 = c1 :=
        Nat.eq_of_mul_eq_mul_right hg (by rw [add_mul, hc1, hb1, ha1, hrel])
      exact ⟨c1, by omega, hcmax a1 b1 c1 ha1pos hb1pos hcop hsum⟩
  have hA0le : A0 ≤ G * W :=
    calc A0 = a1 * g := ha1.symm
      _ ≤ W * G := Nat.mul_le_mul haW hgG
      _ = G * W := mul_comm _ _
  have hyA : y ≤ A0 := Nat.le_self_pow (by omega) y
  rcases hWd with hW | hW
  · -- An exceptional triple: `y` is bounded.
    left
    exact hyd.trans (Nat.pow_le_pow_left (hyA.trans (hA0le.trans (Nat.mul_le_mul_left G hW))) d)
  right
  -- The radical is at most `y · |R(y)| · rad(d^d n!) ≤ CR · d · 4^n · y^(j-1)`.
  set Rb := y * (CR * y ^ (j - 2)) * (d * 4 ^ n) with hRbdef
  have hrad : radical (a1 * b1 * c1) ≤ Rb := by
    have hra : radical a1 ≤ y := by
      refine (radical_le_of_dvd (Nat.div_dvd_of_dvd hdvdA) hA0.ne').trans ?_
      rw [hA0def, radical_pow y (by omega)]
      exact radical_le_self hy0
    have hrb : radical b1 ≤ CR * y ^ (j - 2) :=
      (radical_le_self hb1pos.ne').trans ((Nat.div_le_self _ _).trans ((natAbs_eval_le R hy).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hy (by omega)))))
    have hrc : radical c1 ≤ d * 4 ^ n := by
      refine (radical_le_of_dvd (Nat.div_dvd_of_dvd hdvdN) hN0pos.ne').trans ?_
      refine (radical_le_of_dvd hN0dvd (by positivity)).trans ?_
      refine (radical_mul_le _ _).trans (Nat.mul_le_mul ?_ (radical_factorial_le n))
      rw [radical_pow d hd0]
      exact radical_le_self hd0
    calc radical (a1 * b1 * c1) ≤ radical (a1 * b1) * radical c1 := radical_mul_le _ _
      _ ≤ radical a1 * radical b1 * radical c1 := Nat.mul_le_mul_right _ (radical_mul_le _ _)
      _ ≤ Rb := Nat.mul_le_mul (Nat.mul_le_mul hra hrb) hrc
  -- Raise `W ≤ Rb^(1+ε)` to the power `2d`.
  have hW2 : W ^ (2 * d) ≤ Rb ^ (2 * d + 1) := by
    have h1 : (W : ℝ) ≤ (Rb : ℝ) ^ (1 + ε) :=
      hW.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrad) (by positivity))
    have h2 : (W : ℝ) ^ (2 * d) ≤ ((Rb : ℝ) ^ (1 + ε)) ^ (2 * d) :=
      pow_le_pow_left₀ (by positivity) h1 _
    rw [← Real.rpow_natCast ((Rb : ℝ) ^ (1 + ε)), ← Real.rpow_mul (by positivity)] at h2
    have h3 : (1 + ε) * ((2 * d : ℕ) : ℝ) = ((2 * d + 1 : ℕ) : ℝ) := by
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
      rw [hεdef]
      push_cast
      field_simp
    rw [h3, Real.rpow_natCast] at h2
    exact_mod_cast h2
  have key : y ^ (j * (2 * d)) ≤ G ^ (2 * d) * Rb ^ (2 * d + 1) :=
    calc y ^ (j * (2 * d)) = A0 ^ (2 * d) := by rw [hA0def, pow_mul]
      _ ≤ (G * W) ^ (2 * d) := Nat.pow_le_pow_left hA0le _
      _ = G ^ (2 * d) * W ^ (2 * d) := mul_pow _ _ _
      _ ≤ G ^ (2 * d) * Rb ^ (2 * d + 1) := Nat.mul_le_mul_left _ hW2
  have hRb : Rb = CR * d * 4 ^ n * y ^ (j - 1) := by
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    rw [hRbdef, hj', show j' + 2 - 2 = j' by omega, show j' + 2 - 1 = j' + 1 by omega]
    ring
  have hexp : (d + 1) + (j - 1) * (2 * d + 1) ≤ j * (2 * d) := by
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hjd : j' + 1 ≤ d := by omega
    rw [hj', show j' + 1 - 1 = j' by omega,
      show d + 1 + j' * (2 * d + 1) = j' * (2 * d) + (j' + d + 1) by ring,
      show (j' + 1) * (2 * d) = j' * (2 * d) + 2 * d by ring]
    exact Nat.add_le_add_left (by omega) _
  have hY : 0 < y ^ ((j - 1) * (2 * d + 1)) := by positivity
  have hmain : y ^ (d + 1) * y ^ ((j - 1) * (2 * d + 1)) ≤
      (K3 * (4 ^ (2 * d + 1)) ^ n) * y ^ ((j - 1) * (2 * d + 1)) :=
    calc y ^ (d + 1) * y ^ ((j - 1) * (2 * d + 1))
        = y ^ ((d + 1) + (j - 1) * (2 * d + 1)) := (pow_add _ _ _).symm
      _ ≤ y ^ (j * (2 * d)) := Nat.pow_le_pow_right hy hexp
      _ ≤ G ^ (2 * d) * Rb ^ (2 * d + 1) := key
      _ = (K3 * (4 ^ (2 * d + 1)) ^ n) * y ^ ((j - 1) * (2 * d + 1)) := by
        rw [hRb, hK3]; ring
  calc n ! ≤ y ^ d := hyd
    _ ≤ y ^ (d + 1) := Nat.pow_le_pow_right hy (by omega)
    _ ≤ K3 * (4 ^ (2 * d + 1)) ^ n := Nat.le_of_mul_le_mul_right hmain hY
end Erdos393Proof
