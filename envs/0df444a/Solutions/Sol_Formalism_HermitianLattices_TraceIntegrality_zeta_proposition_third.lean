-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_third
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:34.11573+00:00
-- url     : https://prove2.me/submissions/76bb8036-c057-498d-8af9-202ad0cda6e3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentArithmeticBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
private lemma zii_plus_nonneg {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) (i : Fin (κ + 1)) :
    0 ≤ plus lam i := by
  simp only [plus]
  exact sub_nonneg.2 (h (Fin.le_last i))
private lemma zii_plus0_le {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) :
    plus lam 0 ≤ wt (plus lam) := by
  unfold wt
  exact Finset.single_le_sum (f := plus lam) (fun i _ => zii_plus_nonneg lam h i) (Finset.mem_univ 0)
private lemma positive_part_head_le_weight {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) :
    0 ≤ plus lam 0 ∧ plus lam 0 ≤ wt (plus lam) := ⟨zii_plus_nonneg lam h 0, zii_plus0_le lam h⟩
private lemma ziii_log {a L v x : ℝ} (ha : 1 ≤ a) (hv : 1 ≤ v) (hL : 1 ≤ L)
    (hlog : Real.log (a * v) ≤ L) (hx0 : 0 < x) (hx : x ≤ 7 * a ^ 2) : Real.log x ≤ 8 * L := by
  have ha0 : 0 < a := by linarith
  have h1 : Real.log x ≤ Real.log (7 * a ^ 2) := Real.log_le_log hx0 hx
  have h2 : Real.log (7 * a ^ 2) = Real.log 7 + 2 * Real.log a := by
    rw [Real.log_mul (by norm_num) (pow_pos ha0 2).ne', Real.log_pow, Nat.cast_ofNat]
  have h3 : Real.log 7 ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 7)
    linarith
  have h4 : Real.log a ≤ L := by
    have : Real.log a ≤ Real.log (a * v) := Real.log_le_log ha0 (by nlinarith)
    linarith
  linarith
private lemma ziii_place {C₀ K b' S L lkv logT W lst lg U : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hlkv : 0 ≤ lkv) (hT : 0 ≤ logT)
    (hW : W ≤ U + 4 * K * (b' + S)) (hlg : lg ≤ 8 * L) (hlst : lst ≤ (2 + C₀) * (b' + S)) :
    W * (C₀ * lkv) + K ^ 2 * lg + lst * logT ≤
      U * (C₀ * lkv) + (4 * C₀ * K * (b' + S) * lkv + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have h0 : 0 ≤ C₀ * lkv := mul_nonneg hC hlkv
  have h1 := mul_le_mul_of_nonneg_right hW h0
  have h2 := mul_le_mul_of_nonneg_left hlg (sq_nonneg K)
  have h3 := mul_le_mul_of_nonneg_right hlst hT
  linarith [h1, h2, h3]
private lemma ziii_top {C₀ K a b' S L v logT W p lst At bt : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hKa : K ≤ a) (hb1 : 1 ≤ b') (hba : b' ≤ a) (hS : 0 ≤ S) (hSb : S ≤ b') (hL : 1 ≤ L) (hv : 1 ≤ v)
    (hlog : Real.log (a * v) ≤ L) (hT : 0 ≤ logT) (hp0 : 0 ≤ p) (hpW : p ≤ W)
    (hA2 : At ≤ 2 * a) (hbt2 : bt ≤ 2 * b') (hW : W ≤ At + K * (bt + S)) (hl : lst ≤ bt) :
    W * (C₀ * Real.log (K * v)) + K ^ 2 * Real.log (p + K) + lst * logT ≤
      2 * a * (C₀ * Real.log (K * v)) + (4 * C₀ * K * (b' + S) * Real.log (K * v)
        + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (K * v) := Real.log_nonneg (by nlinarith)
  have hbS : bt + S ≤ 3 * a := by linarith
  have hKbt : K * (bt + S) ≤ a * (3 * a) :=
    (mul_le_mul_of_nonneg_left hbS hK0).trans (mul_le_mul_of_nonneg_right hKa (by linarith))
  have hW' : W ≤ 2 * a + 4 * K * (b' + S) := by
    have : K * (bt + S) ≤ K * (4 * (b' + S)) := mul_le_mul_of_nonneg_left (by linarith) hK0
    linarith
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlg : Real.log (p + K) ≤ 8 * L :=
    ziii_log (by linarith) hv hL hlog (by linarith) (by nlinarith)
  have hlst : lst ≤ (2 + C₀) * (b' + S) := by
    nlinarith [mul_nonneg hC (by linarith : (0:ℝ) ≤ b' + S)]
  have := ziii_place (U := 2 * a) hC hK hlkv hT hW' hlg hlst
  linarith
private lemma ziii_other {C₀ K a b' S L v logT W p lst : ℝ} (hC : 0 ≤ C₀) (hK : 1 ≤ K)
    (hKa : K ≤ a) (hb1 : 1 ≤ b') (hba : b' ≤ a) (hS : 0 ≤ S) (hSb : S ≤ b') (hL : 1 ≤ L) (hv : 1 ≤ v)
    (hlog : Real.log (a * v) ≤ L) (hT : 0 ≤ logT) (hp0 : 0 ≤ p) (hpW : p ≤ W)
    (hW : W ≤ (K + 3) * S) (hl : lst ≤ C₀ * S) :
    W * (C₀ * Real.log (K * v)) + K ^ 2 * Real.log (p + K) + lst * logT ≤
      0 + (4 * C₀ * K * (b' + S) * Real.log (K * v)
        + (2 + C₀) * (b' + S) * logT + 8 * K ^ 2 * L) := by
  have hK0 : 0 ≤ K := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (K * v) := Real.log_nonneg (by nlinarith)
  have hW' : W ≤ 0 + 4 * K * (b' + S) := by
    have h1 : 1 * S ≤ K * S := mul_le_mul_of_nonneg_right hK hS
    have h2 : 0 ≤ K * b' := mul_nonneg hK0 (by linarith)
    nlinarith
  have hK3 : K + 3 ≤ 4 * a := by linarith
  have hSa : S ≤ a := by linarith
  have hKS : (K + 3) * S ≤ 4 * a * a := mul_le_mul hK3 hSa hS (by linarith)
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlg : Real.log (p + K) ≤ 8 * L :=
    ziii_log (by linarith) hv hL hlog (by linarith) (by nlinarith)
  have hlst : lst ≤ (2 + C₀) * (b' + S) := by
    nlinarith [mul_nonneg hC (by linarith : (0:ℝ) ≤ b')]
  have := ziii_place (U := 0) hC hK hlkv hT hW' hlg hlst
  linarith
private lemma final_part_arithmetic_bound {C₀ nT f a lkv K b' S logT L : ℝ} (hC : 0 ≤ C₀) (hnT : 0 ≤ nT) (hf : 0 ≤ f)
    (ha : 0 ≤ a) (hlkv : 0 ≤ lkv) (hK : 0 ≤ K) (hbS : 0 ≤ b' + S) (hT : 0 ≤ logT) (hL : 0 ≤ L) :
    nT * (2 * a * (C₀ * lkv)) + f * (4 * C₀ * K * (b' + S) * lkv + (2 + C₀) * (b' + S) * logT
        + 8 * K ^ 2 * L) ≤
      (8 + 4 * C₀) * nT * a * lkv + (8 + 4 * C₀) * f * (b' + S) * (K * lkv + logT)
        + (8 + 4 * C₀) * f * K ^ 2 * L := by
  have p1 : 0 ≤ nT * a * lkv := mul_nonneg (mul_nonneg hnT ha) hlkv
  have q1 : 0 ≤ C₀ * (nT * a * lkv) := mul_nonneg hC p1
  have p2 : 0 ≤ f * (b' + S) * K * lkv := mul_nonneg (mul_nonneg (mul_nonneg hf hbS) hK) hlkv
  have p3 : 0 ≤ f * (b' + S) * logT := mul_nonneg (mul_nonneg hf hbS) hT
  have q3 : 0 ≤ C₀ * (f * (b' + S) * logT) := mul_nonneg hC p3
  have q4 : 0 ≤ C₀ * (f * K ^ 2 * L) := mul_nonneg hC (mul_nonneg (mul_nonneg hf (sq_nonneg K)) hL)
  linarith [p1, q1, p2, p3, q3, q4]
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : PropZ_iii := by
  intro C₀ hC
  refine ⟨8 + 4 * C₀, ?_⟩
  intro ι X _ _ _ _ TT κ m t N lam A bt a b' L v logT logg eta S muMaxM muMaxV hN hanti hTT hWT hlT
    hWo hlo hex hV
  obtain ⟨c, hc⟩ := hex
  have hL := hN.one_le_L
  have hv := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT := hN.logT_nonneg
  have hS := hN.S_nonneg
  have ha : 1 ≤ a := le_trans hb1 hba
  have hmt : (0:ℝ) ≤ (m : ℝ) * t := by positivity
  have hSb : S ≤ b' := by have := hN.small; have := hN.eta_nonneg; linarith
  have hKN : (κ : ℝ) + 1 ≤ N := by
    have : κ + 1 ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hNb : (N : ℝ) ≤ b' := by
    have h1 := hN.lin
    have h2 : (N : ℝ) * 1 ≤ N * L := mul_le_mul_of_nonneg_left hL hN0
    linarith
  have hK1 : (1:ℝ) ≤ (κ : ℝ) + 1 := by
    have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
    linarith
  have hKa : (κ : ℝ) + 1 ≤ a := by linarith
  have hlkv : 0 ≤ Real.log (((κ : ℝ) + 1) * v) := Real.log_nonneg (by nlinarith)
  have key : ∀ ρ, ((wt (plus (lam ρ)) : ℝ) * (C₀ * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus (lam ρ) 0 : ℝ) + (κ : ℝ) + 1)
        + |(lam ρ (Fin.last κ) : ℝ)| * logT) ≤
      (if ρ ∈ TT then 2 * a * (C₀ * Real.log (((κ : ℝ) + 1) * v)) else 0)
        + (4 * C₀ * ((κ : ℝ) + 1) * (b' + S) * Real.log (((κ : ℝ) + 1) * v)
          + (2 + C₀) * (b' + S) * logT + 8 * ((κ : ℝ) + 1) ^ 2 * L) := by
    intro ρ
    obtain ⟨hp0, hpW⟩ := positive_part_head_le_weight (lam ρ) (hanti ρ)
    have hp0' : (0:ℝ) ≤ (plus (lam ρ) 0 : ℝ) := by exact_mod_cast hp0
    have hpW' : (plus (lam ρ) 0 : ℝ) ≤ (wt (plus (lam ρ)) : ℝ) := by exact_mod_cast hpW
    rw [add_assoc ((plus (lam ρ) 0 : ℤ) : ℝ) (κ : ℝ) 1]
    by_cases hρ : ρ ∈ TT
    · obtain ⟨hA1, hA2, hbt1, hbt2⟩ := hTT ρ hρ
      rw [if_pos hρ]
      exact ziii_top hC hK1 hKa hb1 hba hS hSb hL hv hN.log_av hT hp0' hpW' hA2 hbt2 (hWT ρ hρ)
        (hlT ρ hρ)
    · rw [if_neg hρ]
      exact ziii_other hC hK1 hKa hb1 hba hS hSb hL hv hN.log_av hT hp0' hpW' (hWo ρ hρ) (hlo ρ hρ)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun ρ _ => key ρ)
  have hrhs : ∀ x y : ℝ, ∑ ρ : ι, ((if ρ ∈ TT then x else 0) + y)
      = (TT.card : ℝ) * x + (Fintype.card ι : ℝ) * y := by
    intro x y
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
  rw [hrhs] at hsum
  refine le_trans (le_trans hc (le_trans (hV c) hsum)) ?_
  exact final_part_arithmetic_bound hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hlkv (by linarith)
    (by linarith) hT (by linarith)
end Formalism.HermitianLattices.TraceIntegrality
