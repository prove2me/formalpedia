-- Prove2me | solution 1 for CatalyticTreeEval.Main.corollary_4_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:18:32.291494+00:00
-- url     : https://prove2.me/submissions/935f17f7-c747-4337-9d22-0d147f8dbff2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CatalyticTreeEval_Main_corollary_4_2
import Theorems.Thm_CatalyticTreeEval_Main_corollary_3_11
import Theorems.Thm_CatalyticTreeEval_Main_lemma_3_19
import Theorems.Thm_CatalyticTreeEval_Main_fixed_prime_coding_completion
import Theorems.Thm_CatalyticTreeEval_Main_bare_tree_input_simulation
import Theorems.Thm_CatalyticTreeEval_Main_corollary_4_7_resource_estimates

set_option autoImplicit false

open CatalyticTreeEval.Main

theorem solution :
    ∀ ε : ℝ, 0 < ε →
    ∃ (M : Machine) (Cs Cc Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (h l : ℕ), 0 < h → 0 < l → ∀ I : Tree l h,
      ComputesPrefix M I.encode (bits l I.value.val)
        (Cs * (l + h : ℝ)) (exp₂ (Cc * (l : ℝ) ^ ε))
        (Ct * (2 : ℝ) ^ (q * (l + h))) := by
  have log₂_nat_nonneg : ∀ n : ℕ, 0 ≤ log₂ n := by
    intro n
    exact div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  have cp_mono : ∀ {N : Machine} {x y : List Bool} {S C T S' C' T' : ℝ},
      S ≤ S' → C ≤ C' → T ≤ T' → ComputesPrefix N x y S C T →
      ComputesPrefix N x y S' C' T' := by
    intro N x y S C T S' C' T' hS hC hT hc τ hτ
    have hceilC : ⌈C⌉₊ ≤ ⌈C'⌉₊ := Nat.ceil_mono hC
    obtain ⟨t, c, hrun, hstate, hout, hrest, hwork, htime, hhead⟩ :=
      hc τ (le_trans hceilC hτ)
    have hceilS : ⌈S⌉₊ ≤ ⌈S'⌉₊ := Nat.ceil_mono hS
    refine ⟨t, c, hrun, hstate, hout, hrest, ?_, le_trans htime hT, ?_⟩
    · intro u hu d hd
      exact lt_of_lt_of_le (hwork u hu d hd) hceilS
    · intro u hu d hd
      exact lt_of_lt_of_le (hhead u hu d hd) hceilC
  intro ε hε
  let t : ℕ := max 2 ⌈3 / ε⌉₊
  let p : Fin t → ℕ := firstOddPrimes t
  have ht : 2 ≤ t := by simp [t]
  have hp : OddPrimeData p := by
    constructor
    · refine ⟨by omega, ?_, ?_⟩
      · intro i
        exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
      · intro i j hij
        apply Fin.ext
        change Nat.nth Nat.Prime (i.val + 1) = Nat.nth Nat.Prime (j.val + 1) at hij
        have hh := Nat.nth_injective Nat.infinite_setOfPred_prime hij
        omega
    · intro i
      apply Nat.Prime.odd_of_ne_two (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _)
      intro heq
      have h0 : Nat.nth Nat.Prime 0 = 2 := by
        have h := Nat.nth_count Nat.prime_two
        norm_num [Nat.count] at h
        exact h
      change Nat.nth Nat.Prime (i.val + 1) = 2 at heq
      have hlt := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.succ_pos i.val)
      rw [h0, heq] at hlt
      exact (lt_irrefl 2 hlt)
  obtain ⟨h311, _⟩ := corollary_3_11
  obtain ⟨MV, Cd, Cv, hCd, hCv, hvectors⟩ := h311 t p ht hp
  obtain ⟨MD, Csd, Ctd, qd, hCsd, hCtd, hqd, hdecoder0⟩ := lemma_3_19
  obtain ⟨k0, D0, hk0, _, hD0, hprint0⟩ := hdecoder0 t p hp
  have hdecoder : ∃ (k : ℕ) (D : Decoder (modulus p) k), k ≤ 3 ^ t ∧
      IsDecoder (sumset (canonical p (modulus p))) D ∧
      (∀ j z, PrintsIn MD (decoderRequest (primeCode p) j.val z.val)
        (decoderOutput D j z) (Csd * log₂ (modulus p))
        (Ctd * (1 + log₂ (modulus p)) ^ qd)) :=
    ⟨k0, D0, hk0, hD0, hprint0⟩
  obtain ⟨F, domain, MV', MD', MP, A, r, k, Csl, Ch, Cht,
      hA, hr, hCsl, hCh, hCht, hframe, hFl, hparam⟩ :=
    fixed_prime_coding_completion p hp MV MD Cd Cv Csd Ctd qd
      hCd hCv hCsd hCtd hqd hvectors hdecoder
  obtain ⟨M0, Cs0, Cc0, Ct0, B, q0, hCs0, hCc0, hCt0, hB, hq0, hcomp0⟩ :=
    corollary_4_2 F domain MV' MD' A hA hframe
  obtain ⟨M, Cw, Ctw, qw, hCw, hCtw, hqw, hcomp1⟩ :=
    bare_tree_input_simulation F domain M0 MP Ch Cht r hCh hCht hr hparam
  have hk : k ≤ 3 ^ t := (hFl 1 (by omega)).2.2.2.2.1
  have hF : ∀ l : ℕ, 1 ≤ l →
      (F (natCode l)).m = modulus p ∧
      (F (natCode l)).l = l ∧
      (F (natCode l)).k = k ∧
      ((F (natCode l)).d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
        (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
      ((F (natCode l)).s : ℝ) ≤ Csl * l := by
    intro l hl
    obtain ⟨-, hm, hl', hk', -, hd, hs⟩ := hFl l hl
    exact ⟨hm, hl', hk', hd, hs⟩
  obtain ⟨Cs, Cc, Ct, q, hCs, hCc, hCt, hq, hest⟩ :=
    corollary_4_7_resource_estimates ε hε p hp rfl F k Cd Csl hCd hCsl hk hF
      Cs0 Cc0 Ct0 B Cw Ctw q0 qw hCs0 hCc0 hCt0 hB hCw hCtw hq0 hqw
  refine ⟨M, Cs, Cc, Ct, q, hCs, hCc, hCt, hq, ?_⟩
  intro h l hh hl I
  let a := natCode l
  have ha : a ∈ domain := (hFl l (by omega)).1
  have hla : (F a).l = l := (hFl l (by omega)).2.2.1
  have hcomp0a := hcomp0 a ha h hh
  have hcomp1a := hcomp1 a ha h hh
  rw [hla] at hcomp0a hcomp1a
  have hlogm : 0 ≤ log₂ (F a).m := log₂_nat_nonneg _
  have hS : 0 ≤ Cs0 * ((F a).l + h * (lg (F a).k + log₂ (F a).m) + (F a).s) := by
    have hklog : 0 ≤ log₂ (((F a).k + 1 : ℕ) : ℝ) :=
      log₂_nat_nonneg ((F a).k + 1)
    have hklog' : 0 ≤ log₂ ((F a).k + 1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hklog
    have hlg : 0 ≤ lg (F a).k := by
      unfold lg
      linarith
    have hmul : 0 ≤ (h : ℝ) * (lg (F a).k + log₂ (F a).m) :=
      mul_nonneg (by positivity) (add_nonneg hlg hlogm)
    have hsum : 0 ≤ ((F a).l : ℝ) + (h : ℝ) *
        (lg (F a).k + log₂ (F a).m) + ((F a).s : ℝ) := by
      positivity
    exact mul_nonneg hCs0.le hsum
  have hC : 0 ≤ Cc0 * (F a).d * (1 + log₂ ((F a).d * (F a).m)) := by
    have hlog0 : 0 ≤ log₂ ((((F a).d * (F a).m : ℕ) : ℝ)) :=
      log₂_nat_nonneg ((F a).d * (F a).m)
    have hlog : 0 ≤ log₂ ((F a).d * (F a).m : ℝ) := by
      simpa only [Nat.cast_mul] using hlog0
    have hone : (0 : ℝ) ≤ 1 + log₂ ((F a).d * (F a).m) := by linarith
    exact mul_nonneg (mul_nonneg hCc0.le (by positivity)) hone
  have hT : 0 ≤ Ct0 * (B * (F a).k) ^ h *
      ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q0 := by
    have hk0 : (0 : ℝ) ≤ (F a).k := by positivity
    have hBk : (0 : ℝ) ≤ B * (F a).k := mul_nonneg hB.le hk0
    have hsum : (0 : ℝ) ≤ (2 : ℝ) ^ (F a).l + (F a).k +
        (F a).d + (2 : ℝ) ^ (F a).s := by positivity
    exact mul_nonneg (mul_nonneg hCt0.le (pow_nonneg hBk _)) (pow_nonneg hsum _)
  rw [hla] at hS hT
  have hbase := hcomp0a I
  have hw := hcomp1a I _ _ _ hS hC hT hbase
  obtain ⟨hspace, hcat, htime⟩ := hest h l hh hl
  rw [hla] at hspace htime
  have hfinal := cp_mono hspace hcat htime hw
  exact hfinal