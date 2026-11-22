-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_second
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:33.652145+00:00
-- url     : https://prove2.me/submissions/1a2cb3eb-68c8-47d4-98ae-d67273cfb367

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
private lemma zii_log_le {a L v W : ℝ} (ha : 1 ≤ a) (hv : 1 ≤ v) (hL : 1 ≤ L)
    (hlog : Real.log (a * v) ≤ L) (hW0 : 0 < W) (hW : W ≤ 9 * a ^ 2) : Real.log W ≤ 10 * L := by
  have ha0 : 0 < a := by linarith
  have h1 : Real.log W ≤ Real.log (9 * a ^ 2) := Real.log_le_log hW0 hW
  have h2 : Real.log (9 * a ^ 2) = Real.log 9 + 2 * Real.log a := by
    rw [Real.log_mul (by norm_num) (pow_pos ha0 2).ne', Real.log_pow, Nat.cast_ofNat]
  have h3 : Real.log 9 ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 9)
    linarith
  have h4 : Real.log a ≤ L := by
    have : Real.log a ≤ Real.log (a * v) := Real.log_le_log ha0 (by nlinarith)
    linarith
  linarith
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : PropZ_ii := by
  intro C₀ hC
  refine ⟨11 + C₀, ?_⟩
  intro ι X _ _ _ _ TT κ m t N lam A bt a b' L v logT logg eta S muM muV muDelta muNabla muMaxNabla
    hN hanti hTT hwt hwtp hwtp' hwt' hM hV hD hNab hMax
  have hL1 := hN.one_le_L
  have hv1 := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hS0 := hN.S_nonneg
  have hκ0 : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
  have hK1 : (1:ℝ) ≤ (κ:ℝ) + 1 := by linarith
  have hK0 : (0:ℝ) < (κ:ℝ) + 1 := by linarith
  have hKN : (κ:ℝ) + 1 ≤ N := by
    have : κ + 1 ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hNL : (N:ℝ) * L ≤ b' := by linarith [hN.lin]
  have hNNL : (N:ℝ) ≤ N * L := by nlinarith
  have hKb : (κ:ℝ) + 1 ≤ b' := by linarith
  have hKa : (κ:ℝ) + 1 ≤ a := le_trans hKb hba
  have hSb : S ≤ b' := by
    have := hN.small
    have := hN.eta_nonneg
    have : (0:ℝ) ≤ (m:ℝ) * t := by positivity
    linarith
  have ha1 : 1 ≤ a := le_trans hb1 hba
  have haa : a ≤ a ^ 2 := by nlinarith
  have hlogK0 : 0 ≤ Real.log ((κ:ℝ) + 1) := Real.log_nonneg hK1
  have hKbS : 0 ≤ ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) :=
    mul_nonneg (mul_nonneg hK0.le (by linarith)) hlogK0
  have hZ4 : ∀ ρ, MeanSquareWeightBound (lam ρ) ≤ (if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
      + (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
    intro ρ
    have hp0 : (0:ℝ) ≤ (plus (lam ρ) 0 : ℝ) := by exact_mod_cast zii_plus_nonneg (lam ρ) (hanti ρ) 0
    have hpW : (plus (lam ρ) 0 : ℝ) ≤ (wt (plus (lam ρ)) : ℝ) := by
      exact_mod_cast zii_plus0_le (lam ρ) (hanti ρ)
    unfold MeanSquareWeightBound
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      obtain ⟨h1, h2, h3, h4⟩ := hTT ρ hρ
      have hw := hwtp ρ hρ
      have e1 : ((κ:ℝ) + 1) * (bt ρ + S) ≤ ((κ:ℝ) + 1) * (2 * (b' + S)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0.le
      have hWb : (wt (plus (lam ρ)) : ℝ) ≤ 2 * a + 2 * (((κ:ℝ) + 1) * (b' + S)) := by linarith
      have e2 : ((κ:ℝ) + 1) * (b' + S) ≤ a * (2 * a) :=
        mul_le_mul hKa (by linarith) (by linarith) (by linarith)
      have hlog : Real.log ((plus (lam ρ) 0 : ℝ) + (κ:ℝ) + 1) ≤ 10 * L :=
        zii_log_le ha1 hv1 hL1 hN.log_av (by linarith) (by nlinarith)
      have f1 := mul_le_mul_of_nonneg_right hWb hlogK0
      have f2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((κ:ℝ) + 1))
      nlinarith [f1, f2, hKbS]
    · rw [if_neg hρ]
      have hw := hwtp' ρ hρ
      have e1 : ((κ:ℝ) + 1 + 3) * S ≤ 4 * (((κ:ℝ) + 1) * (b' + S)) := by nlinarith
      have e2 : ((κ:ℝ) + 1 + 3) * S ≤ (4 * a) * a := mul_le_mul (by linarith) (by linarith) hS0 (by linarith)
      have hlog : Real.log ((plus (lam ρ) 0 : ℝ) + (κ:ℝ) + 1) ≤ 10 * L :=
        zii_log_le ha1 hv1 hL1 hN.log_av (by linarith) (by nlinarith)
      have f1 := mul_le_mul_of_nonneg_right (hw.trans e1) hlogK0
      have f2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ((κ:ℝ) + 1))
      nlinarith [f1, f2, hKbS]
  have hsumZ4 : ∑ ρ, MeanSquareWeightBound (lam ρ) ≤ (TT.card : ℝ) * (2 * a * Real.log ((κ:ℝ) + 1))
      + (Fintype.card ι : ℝ) * (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)
        + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
    have e1 : ∑ ρ, (if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
        = (TT.card : ℝ) * (2 * a * Real.log ((κ:ℝ) + 1)) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have e2 : ∑ _ρ : ι, (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L)
        = (Fintype.card ι : ℝ) * (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)
          + 10 * ((κ:ℝ) + 1) ^ 2 * L) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ∑ ρ, MeanSquareWeightBound (lam ρ) ≤ ∑ ρ, ((if ρ ∈ TT then 2 * a * Real.log ((κ:ℝ) + 1) else 0)
          + (4 * ((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1) + 10 * ((κ:ℝ) + 1) ^ 2 * L)) :=
          Finset.sum_le_sum fun ρ _ => hZ4 ρ
      _ = _ := by rw [Finset.sum_add_distrib, e1, e2]
  have hwtbound : ∀ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
      ≤ (if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0) + (1 + C₀) * S * logT := by
    intro ρ
    have h3 : 0 ≤ C₀ * S * logT := mul_nonneg (mul_nonneg hC hS0) hT0
    have h4 : 0 ≤ S * logT := mul_nonneg hS0 hT0
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      have h := hwt ρ hρ
      have h1 : (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) ≤ A ρ / ((κ:ℝ) + 1) + S := by
        rw [div_le_iff₀ hK0, add_mul, div_mul_cancel₀ _ hK0.ne']
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hT0
      linarith
    · rw [if_neg hρ]
      have h := hwt' ρ hρ
      have h1 : (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) ≤ C₀ * S := by
        rw [div_le_iff₀ hK0]
        linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hT0
      linarith
  have hsumwt : ∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
      ≤ ∑ τ ∈ TT, A τ / ((κ:ℝ) + 1) * logT + (Fintype.card ι : ℝ) * ((1 + C₀) * S * logT) := by
    have e1 : ∑ ρ, (if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0)
        = ∑ τ ∈ TT, A τ / ((κ:ℝ) + 1) * logT := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have e2 : ∑ _ρ : ι, (1 + C₀) * S * logT = (Fintype.card ι : ℝ) * ((1 + C₀) * S * logT) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT
        ≤ ∑ ρ, ((if ρ ∈ TT then A ρ / ((κ:ℝ) + 1) * logT else 0) + (1 + C₀) * S * logT) :=
          Finset.sum_le_sum fun ρ _ => hwtbound ρ
      _ = _ := by rw [Finset.sum_add_distrib, e1, e2]
  have hmean : muM = -(∑ ρ, (wt (lam ρ) : ℝ) / ((κ:ℝ) + 1) * logT) + ∑ ρ, muDelta ρ := by
    rw [hM]
    have hc : (0:ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
    unfold mean
    simp only [hV]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hc.ne']
  have hDel : -(∑ ρ, MeanSquareWeightBound (lam ρ)) ≤ ∑ ρ, muDelta ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun ρ _ => by rw [hD ρ]; linarith [hNab ρ, hMax ρ]
  have hcard0 : (0:ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have n1 : 0 ≤ (TT.card : ℝ) * a * Real.log ((κ:ℝ) + 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hlogK0
  have m1 : 0 ≤ C₀ * ((TT.card : ℝ) * a * Real.log ((κ:ℝ) + 1)) := mul_nonneg hC n1
  have n2 : 0 ≤ (Fintype.card ι : ℝ) * S * logT := mul_nonneg (mul_nonneg hcard0 hS0) hT0
  have n3 : 0 ≤ (Fintype.card ι : ℝ) * (((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1)) :=
    mul_nonneg hcard0 hKbS
  have m3 : 0 ≤ C₀ * ((Fintype.card ι : ℝ) * (((κ:ℝ) + 1) * (b' + S) * Real.log ((κ:ℝ) + 1))) :=
    mul_nonneg hC n3
  have n4 : 0 ≤ (Fintype.card ι : ℝ) * (((κ:ℝ) + 1) ^ 2 * L) :=
    mul_nonneg hcard0 (mul_nonneg (sq_nonneg _) (by linarith))
  have m4 : 0 ≤ C₀ * ((Fintype.card ι : ℝ) * (((κ:ℝ) + 1) ^ 2 * L)) := mul_nonneg hC n4
  linarith [hmean, hDel, hsumZ4, hsumwt, n1, m1, n2, n3, m3, n4, m4]
end Formalism.HermitianLattices.TraceIntegrality
