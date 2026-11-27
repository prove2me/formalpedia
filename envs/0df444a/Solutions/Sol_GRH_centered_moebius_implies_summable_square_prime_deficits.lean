-- Prove2me | solution 1 for GRH.centered_moebius_implies_summable_square_prime_deficits
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:23:42.819208+00:00
-- url     : https://prove2.me/submissions/2be4f8b0-c416-4bce-8b2b-41ce203a5ee6

import Theorems.Thm_GRH_prime_power_excess_in_a_progression_is_uniformly_square_root
import Theorems.Thm_GRH_grh_implies_psiAP_square_root
import Theorems.Thm_GRH_centered_moebius_at_modulus_iff_dirichlet_zero_free
import Mathlib.Tactic.FieldSimp

open Finset Filter GRH.OneSidedMoebius GRH.FactorialMoebius GRH.SplitPrimeLower GRH.PrimeDeficitMean

private theorem psi_eq (q n : ℕ) : ArtinPrimitiveRoots.psiAP n q 1 = mangoldtWeight q n := by
  classical
  unfold ArtinPrimitiveRoots.psiAP mangoldtWeight
  rw [show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc 0 n,Finset.sum_filter]
  apply sum_congr rfl
  intro i _
  have e : (i:ZMod q)=1 ↔ i ≡ 1 [MOD q] := by simpa only [Nat.cast_one] using ZMod.natCast_eq_natCast_iff i 1 q
  simp only [ArithmeticFunction.vonMangoldt.residueClass,Set.indicator_apply,Set.mem_ofPred_eq,e]

private theorem power_bound (h : centeredBound) (q : ℕ) [NeZero q] (α : ℝ)
    (ha : 1/2<α) : ∃ C : ℝ, 0≤C ∧ ∀ u : ℕ, deficit q ((u:ℝ)^2) ≤ C*((u:ℝ)^2+1)^α := by
  have hg : ∀ (m : ℕ) [NeZero m], rightHalfPlane m := by
    intro m _
    have e := GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free m
    exact e.2.1.mp (e.1.mp (h m))
  obtain ⟨B,hB,hpsi⟩ := GRH.grh_implies_psiAP_square_root hg q 1 (NeZero.ne q) (by simp)
  obtain ⟨K,hK,hpow⟩ := GRH.prime_power_excess_in_a_progression_is_uniformly_square_root
  let d := (α-1/2)/2
  have hd : 0<d := by dsimp [d];linarith
  let C := 2+(q.totient:ℝ)*(B/d^2+K)
  have hC2 : (2:ℝ) ≤ C := by dsimp [C];exact le_add_of_nonneg_right (by positivity)
  have hC : 0 ≤ C := by linarith
  refine ⟨C,hC,fun u => ?_⟩
  let x := (u:ℝ)^2
  have hx : 0 ≤ x := sq_nonneg _
  have ha0 : 0 ≤ α := by linarith
  have hfloor : ⌊x⌋₊ = u^2 := by change ⌊(u:ℝ)^2⌋₊ = _; rw [← Nat.cast_pow,Nat.floor_natCast]
  change max (x-(q.totient:ℝ)*primeWeight q ⌊x⌋₊) 0 ≤ C*(x+1)^α
  apply max_le _ (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
  by_cases hx2 : 2 ≤ x
  · have hx1 : 1 ≤ x := by linarith
    have hlog := Real.log_le_rpow_div hx (ε:=d) hd
    have hlog2 := pow_le_pow_left₀ (Real.log_nonneg hx1) hlog 2
    have hex : x^(1/2:ℝ)*(Real.log x)^2 ≤ x^α/d^2 := by
      calc
        _ ≤ x^(1/2:ℝ)*(x^d/d)^2 := mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = _ := by
          rw [div_pow,← Real.rpow_natCast (x^d),← Real.rpow_mul hx]
          rw [← mul_div_assoc,← Real.rpow_add (by linarith : 0<x)]
          congr 2
          dsimp [d];ring
    have hxp : x^(1/2:ℝ) ≤ x^α := Real.rpow_le_rpow_of_exponent_le hx1 ha.le
    have hf := (abs_le.mp (hpsi x hx2)).1
    rw [psi_eq] at hf
    have hcmp := (hpow q ⌊x⌋₊).2
    rw [hfloor,Nat.cast_pow] at hcmp
    change _ ≤ K*Real.sqrt x at hcmp
    rw [Real.sqrt_eq_rpow] at hcmp
    have hφ : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    have e : x/(q.totient:ℝ) - primeWeight q ⌊x⌋₊ ≤ (B/d^2+K)*x^α := by
      rw [hfloor] at hf ⊢
      calc
        _ ≤ B*x^(1/2:ℝ)*(Real.log x)^2+K*x^(1/2:ℝ) := by linarith only [hf,hcmp]
        _ ≤ B*(x^α/d^2)+K*x^α := by rw [mul_assoc B];exact add_le_add (mul_le_mul_of_nonneg_left hex hB) (mul_le_mul_of_nonneg_left hxp hK)
        _ = _ := by ring
    have h1 := mul_le_mul_of_nonneg_left e hφ.le
    rw [mul_sub,mul_div_cancel₀ _ hφ.ne'] at h1
    apply h1.trans
    calc
      _ ≤ C*x^α := by dsimp [C];nlinarith only [Real.rpow_nonneg hx α]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx (by linarith) ha0) hC
  · have hp : 0≤primeWeight q ⌊x⌋₊ := by
      apply sum_nonneg
      intro i hi
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.1.one_le)
      · rfl
    have hscale : 1≤(x+1)^α := Real.one_le_rpow (by linarith) ha0
    nlinarith only [hscale,mul_le_mul_of_nonneg_left hscale hC,hC2,lt_of_not_ge hx2,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) q.totient) hp]

theorem solution (h : centeredBound) (q : ℕ) [NeZero q] (θ : ℝ) (hθ : 1/2<θ) :
    squareLower q θ ∧ squareMean q θ := by
  obtain ⟨C,hC,H⟩ := power_bound h q θ hθ
  constructor
  · refine ⟨C,hC,fun u => ?_⟩
    have hu := (le_max_left ..).trans (H u)
    change (u:ℝ)^2-(q.totient:ℝ)*primeWeight q ⌊(u:ℝ)^2⌋₊ ≤ _ at hu
    rw [← Nat.cast_pow,Nat.floor_natCast,Nat.cast_pow] at hu
    linarith
  · let β := (θ+1/2)/2
    have hb : 1/2<β := by dsimp [β];linarith
    have hb' : β<θ := by dsimp [β];linarith
    have hb0 : 0≤β := by linarith
    obtain ⟨M,hM,hm⟩ := power_bound h q β hb
    have hs : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(2*β-2*θ-1)) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
    unfold squareMean
    refine Summable.of_nonneg_of_le (f:=fun n : ℕ => (M*2^β)*((n+1:ℕ):ℝ)^(2*β-2*θ-1))
      (fun n => mul_nonneg (le_max_right ..) (Real.rpow_nonneg (by positivity) _)) ?_ (hs.mul_left _)
    intro n
    let u : ℕ := n+1
    have hu : 1≤(u:ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hup : 0<(u:ℝ) := by linarith
    have hscl := Real.rpow_le_rpow (show 0 ≤ (u:ℝ)^2+1 by positivity)
      (show (u:ℝ)^2+1 ≤ 2*(u:ℝ)^2 by nlinarith) hb0
    have he : ((u:ℝ)^2)^β = (u:ℝ)^((2:ℝ)*β) := by
      rw [Real.rpow_mul hup.le,Real.rpow_two]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (sq_nonneg _),he] at hscl
    have h := (hm u).trans (mul_le_mul_of_nonneg_left hscl hM)
    unfold deficitTerm
    calc
      _ ≤ (M*(2^β*(u:ℝ)^((2:ℝ)*β)))*(u:ℝ)^(-2*θ-1) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hup.le _)
      _ = _ := by
        change _ = (M*2^β)*(u:ℝ)^(2*β-2*θ-1)
        rw [show 2*β-2*θ-1 = 2*β+(-2*θ-1) by ring,Real.rpow_add hup];ring
