-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:59:31.429043+00:00
-- url     : https://prove2.me/submissions/92421c93-20e7-49e7-bba2-c75d48a4bf25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Mathlib
import Theorems.Thm_EdgeSublinearMWIS_Main_weighted_stack_qptas
import Theorems.Thm_EdgeSublinearMWIS_Main_stack_simulation


open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EncodingBounds

 theorem natBits_length (n : ℕ) : (natBits n).length ≤ n := by
  simpa only [natBits, List.length_map] using
    (Nat.digits_length_le_iff (by decide : 1 < 2) n).mpr (show n < 2 ^ n from Nat.lt_two_pow_self)

 theorem encodeNat_length (n : ℕ) : (encodeNat n).length ≤ 2 * n + 1 := by
  have h := natBits_length n
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
  omega

 theorem rationalBits_length (r : RationalCode) : 1 ≤ r.bits.length := by
  simp only [RationalCode.bits, encodeInt, List.length_append, List.length_singleton]
  omega

 theorem order_le_data {n : ℕ} (w : Fin n → RationalCode) (ε : RationalCode) :
    n ≤ (rationalData w ε).length := by
  have hsum : (∑ _v : Fin n, 1) ≤ ∑ v : Fin n, (w v).bits.length :=
    Finset.sum_le_sum (fun v hv => rationalBits_length (w v))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  have heq : (rationalData w ε).length = (∑ v, (w v).bits.length) + ε.bits.length := by
    simp [rationalData, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  omega

 theorem graphBits_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphBits G).length ≤ (n + 1) ^ 2 := by
  classical
  have hpart (u : Fin n) : ((List.finRange n).filter (fun v => u < v)).length ≤ n := by
    simpa using (List.length_filter_le (fun v : Fin n => decide (u < v)) (List.finRange n))
  have hsum : (∑ u : Fin n, ((List.finRange n).filter (fun v => u < v)).length) ≤ n * n := by
    calc
      _ ≤ ∑ _u : Fin n, n := Finset.sum_le_sum (fun v hv => hpart v)
      _ = n * n := by simp
  have heq : (graphBits G).length = (encodeNat n).length +
      ∑ u : Fin n, ((List.finRange n).filter (fun v => u < v)).length := by
    simp [graphBits, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn]
  have henc := encodeNat_length n
  nlinarith

 theorem input_length {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
    (weightedInput G w ε).length + 1 ≤ 3 * ((rationalData w ε).length + 1) ^ 2 := by
  have hn := order_le_data w ε
  have hg := graphBits_length G
  simp only [weightedInput, List.length_append]
  nlinarith

end EdgeSublinearMWIS.Main.EncodingBounds


open scoped BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.SimulationEnvelope

 theorem polynomial_simulation (q r d : ℕ) (K k : ℝ) (hK : 0 < K) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (ell t i s : ℕ), 0 ≤ x →
      (t : ℝ) ≤ K * Real.exp (K * x ^ d) + K * (ell + 1 : ℝ) ^ q →
      i + 1 ≤ 3 * (ell + 1) ^ 2 →
      (s : ℝ) ≤ k * (t + i + 1 : ℝ) ^ r →
      (s : ℝ) ≤ C * Real.exp (C * x ^ d) + C * (ell + 1 : ℝ) ^ (max q 2 * r) := by
  let A := K + 4
  let D := k * A ^ r * (2 : ℝ) ^ (r - 1)
  let C := D + (r : ℝ) * K + 1
  have hA : 0 < A := by dsimp [A]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D ≤ C := by
    dsimp [C]
    have hh := mul_nonneg (Nat.cast_nonneg r) hK.le
    linarith
  have hrK : (r : ℝ) * K ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro x ell t i s hx ht hi hs
  let L : ℝ := ell + 1
  let E := Real.exp (K * x ^ d)
  have hL : 1 ≤ L := by dsimp [L]; have hh := Nat.cast_nonneg (α := ℝ) ell; linarith
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hK.le (pow_nonneg hx _))
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  have hpow : L ^ q ≤ L ^ max q 2 := pow_le_pow_right₀ hL (le_max_left _ _)
  have hpow2 : L ^ 2 ≤ L ^ max q 2 := pow_le_pow_right₀ hL (le_max_right _ _)
  have hiR : (i : ℝ) + 1 ≤ 3 * L ^ 2 := by dsimp [L]; exact_mod_cast hi
  have hsum : (t + i + 1 : ℝ) ≤ A * (E + L ^ max q 2) := by
    change (t : ℝ) ≤ K * E + K * L ^ q at ht
    dsimp [A]
    have hP : (0 : ℝ) ≤ L ^ max q 2 := pow_nonneg hL0 _
    nlinarith [mul_le_mul_of_nonneg_left hpow hK.le]
  have hpowSum : (t + i + 1 : ℝ) ^ r ≤ (A * (E + L ^ max q 2)) ^ r :=
    pow_le_pow_left₀ (by positivity) hsum _
  have hadd := add_pow_le hE0 (pow_nonneg hL0 (max q 2)) r
  have hmain : (s : ℝ) ≤ D * (E ^ r + L ^ (max q 2 * r)) := by
    calc
      (s : ℝ) ≤ k * (A * (E + L ^ max q 2)) ^ r := hs.trans (mul_le_mul_of_nonneg_left hpowSum hk.le)
      _ = k * A ^ r * (E + L ^ max q 2) ^ r := by rw [mul_pow]; ring
      _ ≤ k * A ^ r * ((2 : ℝ) ^ (r - 1) * (E ^ r + (L ^ max q 2) ^ r)) :=
        mul_le_mul_of_nonneg_left hadd (by positivity)
      _ = D * (E ^ r + L ^ (max q 2 * r)) := by dsimp [D]; rw [pow_mul]; ring
  have hEr : E ^ r ≤ Real.exp (C * x ^ d) := by
    dsimp [E]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hrK (pow_nonneg hx d)]
  calc
    (s : ℝ) ≤ D * (E ^ r + L ^ (max q 2 * r)) := hmain
    _ ≤ C * Real.exp (C * x ^ d) + C * L ^ (max q 2 * r) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul hDC hEr (pow_nonneg hE0 _) hC.le)
        (mul_le_mul_of_nonneg_right hDC (pow_nonneg hL0 _))
    _ = _ := rfl

end EdgeSublinearMWIS.Main.SimulationEnvelope


open scoped BigOperators
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.EncodingBounds
open EdgeSublinearMWIS.Main.SimulationEnvelope
set_option autoImplicit false

theorem solution :
    ∃ q : ℕ, 0 < q ∧ ∀ C : GraphClass, StronglyEdgeSublinear C →
      ∃ (M : CatalyticMatching.General.Machine) (K : ℝ) (d : ℕ), 0 < K ∧ 0 < d ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode)
          (ε : RationalCode), C n G → 0 < ε.value → ε.value < 1 →
          ∃ (I : Finset (Fin n)) (s : ℕ),
            BitHalts M (weightedInput G w ε) (mask I) s ∧
            G.IsIndepSet (I : Set (Fin n)) ∧
            (1 - (ε.value : ℝ)) * weightedAlpha G (fun v => (w v).value) ≤
              ∑ v ∈ I, ((w v).value : ℝ) ∧
            (s : ℝ) ≤ K * Real.exp
              (K * (((ε.value : ℝ))⁻¹ * logTwo (max 2 n)) ^ d) +
                K * ((rationalData w ε).length + 1 : ℝ) ^ q := by
  obtain ⟨q, hq, hweighted⟩ := weighted_stack_qptas
  obtain ⟨r, hr, hsim⟩ := stack_simulation
  refine ⟨max q 2 * r, Nat.mul_pos (by omega) hr, ?_⟩
  intro C hC
  obtain ⟨P, K, d, hK, hd, hP⟩ := hweighted C hC
  obtain ⟨M, k, hk, hM⟩ := hsim P
  obtain ⟨D, hD, henv⟩ := polynomial_simulation q r d K k hK (by exact_mod_cast hk)
  refine ⟨M, D, d, hD, hd, ?_⟩
  intro n G w ε hG he he1
  obtain ⟨I, t, ht, hind, happrox, htime⟩ := hP n G w ε hG he he1
  obtain ⟨s, hs, hsteps⟩ := hM (weightedInput G w ε) (mask I) t ht
  refine ⟨I, s, hs, hind, happrox, ?_⟩
  have hε : (0 : ℝ) < ε.value := by exact_mod_cast he
  have hlog : 0 ≤ logTwo (max 2 n) := by
    unfold logTwo
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ max 2 n from (by omega))
    · exact Real.log_nonneg (by norm_num)
  apply henv _ (rationalData w ε).length t (weightedInput G w ε).length s
    (mul_nonneg (inv_nonneg.mpr hε.le) hlog) htime (input_length G w ε)
  exact_mod_cast hsteps
