-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.third_zeta_application
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:16.504649+00:00
-- url     : https://prove2.me/submissions/6c9e0de9-05d4-42d5-8747-5451e8d26bbe

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
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
private lemma log_weyl_dimension_bound (n : ℕ) (lam : Fin (n + 1) → ℤ) (h : Antitone lam) :
    Real.log (weylDim lam) ≤ ((n : ℝ) + 1) ^ 2 * Real.log (Wnum lam : ℝ) := by
  have hW1 : (1 : ℝ) ≤ (Wnum lam : ℝ) := by
    have h0 : lam (Fin.last n) ≤ lam 0 := h (Fin.zero_le _)
    have : (1 : ℤ) ≤ Wnum lam := by unfold Wnum; omega
    exact_mod_cast this
  have hfac : ∀ i j : Fin (n + 1), i < j →
      1 ≤ (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ∧
      (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ (Wnum lam : ℝ) := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hd : (1 : ℝ) ≤ ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij'
      linarith
    have h1 : lam j ≤ lam i := h hij.le
    have h2 : lam i ≤ lam 0 := h (Fin.zero_le _)
    have h3 : lam (Fin.last n) ≤ lam j := h (Fin.le_last _)
    have hj : (j : ℕ) ≤ n := j.is_le
    have hnum : (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ))
        = ((lam i - lam j : ℤ) : ℝ) + (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by push_cast; ring
    have h1' : (0 : ℝ) ≤ ((lam i - lam j : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr h1
    constructor
    · rw [le_div_iff₀ (by linarith), hnum]; linarith
    · rw [div_le_iff₀ (by linarith)]
      have h4 : (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ)) ≤ (Wnum lam : ℝ) := by
        have : lam i - lam j + (j : ℤ) - (i : ℤ) ≤ Wnum lam := by unfold Wnum; omega
        exact_mod_cast this
      nlinarith
  have hpos : 0 < weylDim lam := by
    unfold weylDim
    apply prod_pos; intro i _; apply prod_pos; intro j hj
    have := (hfac i j (by simpa using hj)).1
    linarith
  have hle : weylDim lam ≤ (Wnum lam : ℝ) ^ ((n + 1) * (n + 1)) := by
    unfold weylDim
    calc _ ≤ ∏ _i : Fin (n + 1), (Wnum lam : ℝ) ^ (n + 1) := by
          apply prod_le_prod
          · intro i _; apply prod_nonneg; intro j hj
            have := (hfac i j (by simpa using hj)).1
            linarith
          · intro i _
            calc _ ≤ ∏ _j ∈ univ.filter (fun j : Fin (n + 1) => i < j), (Wnum lam : ℝ) := by
                  apply prod_le_prod
                  · intro j hj
                    have := (hfac i j (by simpa using hj)).1
                    linarith
                  · intro j hj
                    exact (hfac i j (by simpa using hj)).2
              _ = (Wnum lam : ℝ) ^ (univ.filter (fun j : Fin (n + 1) => i < j)).card := by
                  rw [prod_const]
              _ ≤ (Wnum lam : ℝ) ^ (n + 1) := by
                  apply pow_le_pow_right₀ hW1
                  calc _ ≤ (univ : Finset (Fin (n + 1))).card := card_filter_le _ _
                    _ = n + 1 := by simp
      _ = _ := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
  calc Real.log (weylDim lam) ≤ Real.log ((Wnum lam : ℝ) ^ ((n + 1) * (n + 1))) :=
        Real.log_le_log hpos hle
    _ = (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (Wnum lam : ℝ) := Real.log_pow _ _
    _ = _ := by push_cast; ring
private lemma arithmetic_bound_at_top {C₀ L logT b' eta S mt nn d M lw ld B bt A : ℝ} (hC : 0 ≤ C₀) (hL : 0 ≤ L)
    (hT : 0 ≤ logT) (hb : 0 ≤ b') (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ mt) (hn : 0 ≤ nn)
    (hM0 : 0 ≤ M) (hM : M ≤ 3 * B + (eta + S)) (hlw : lw ≤ C₀ * L) (hld : ld ≤ (nn + 1) ^ 2 * lw)
    (hbt : bt ≤ 2 * b') (hB : B ≤ bt + eta + S) (hd : A - bt - C₀ * (S + eta + mt) ≤ d) :
    -d * logT + 2 * nn * lw * M + ld ≤ -A * logT + (12 * C₀ + 2) * b' * (logT + (nn + 1) * L)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L) := by
  have h1 : -d * logT ≤ (-A + 2 * b' + C₀ * (S + eta + mt)) * logT :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  have h2 : 2 * nn * lw * M ≤ 2 * nn * (C₀ * L) * M := by gcongr
  have h3 : 2 * nn * (C₀ * L) * M ≤ 2 * nn * (C₀ * L) * (6 * b' + 4 * eta + 4 * S) := by
    gcongr; linarith
  have h4 : ld ≤ (nn + 1) ^ 2 * (C₀ * L) := hld.trans (by gcongr)
  have key : 0 ≤ (-A * logT + (12 * C₀ + 2) * b' * (logT + (nn + 1) * L)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L))
      - ((-A + 2 * b' + C₀ * (S + eta + mt)) * logT
        + 2 * nn * (C₀ * L) * (6 * b' + 4 * eta + 4 * S) + (nn + 1) ^ 2 * (C₀ * L)) := by
    ring_nf; positivity
  linarith
private lemma arithmetic_bound_off_top {C₀ L logT eta S mt nn d M lw ld B : ℝ} (hC : 0 ≤ C₀) (hL : 0 ≤ L)
    (hT : 0 ≤ logT) (he : 0 ≤ eta) (hS : 0 ≤ S) (hmt : 0 ≤ mt) (hn : 0 ≤ nn)
    (hM0 : 0 ≤ M) (hM : M ≤ 3 * B + (eta + S)) (hlw : lw ≤ C₀ * L) (hld : ld ≤ (nn + 1) ^ 2 * lw)
    (hB : B ≤ eta + S) (hd : -(S + eta) - C₀ * mt ≤ d) :
    -d * logT + 2 * nn * lw * M + ld ≤ 0
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L) := by
  have h1 : -d * logT ≤ (S + eta + C₀ * mt) * logT :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  have h2 : 2 * nn * lw * M ≤ 2 * nn * (C₀ * L) * M := by gcongr
  have h3 : 2 * nn * (C₀ * L) * M ≤ 2 * nn * (C₀ * L) * (4 * eta + 4 * S) := by
    gcongr; linarith
  have h4 : ld ≤ (nn + 1) ^ 2 * (C₀ * L) := hld.trans (by gcongr)
  have key : 0 ≤ (0 + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + (nn + 1) * L)
        + (12 * C₀ + 2) * (nn + 1) ^ 2 * L))
      - ((S + eta + C₀ * mt) * logT
        + 2 * nn * (C₀ * L) * (4 * eta + 4 * S) + (nn + 1) ^ 2 * (C₀ * L)) := by
    ring_nf; positivity
  linarith
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : ZetaBoundApplication := by
  intro C₀ hC
  refine ⟨12 * C₀ + 2, ?_⟩
  intro ι _ _ TT n lam sg A bt b' L logT eta S mt logP hL hT hb he hS hmt hI hW hbt hBt hBn hX
    hdt hdn hP
  have hL0 : 0 ≤ L := by linarith
  have hplace : ∀ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT ≤
      (if ρ ∈ TT then -A ρ * logT + (12 * C₀ + 2) * b' * (logT + ((n : ℝ) + 1) * L) else 0)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + (12 * C₀ + 2) * ((n : ℝ) + 1) ^ 2 * L) := by
    intro ρ
    obtain ⟨X, hXc, hXs⟩ := hX ρ
    have hB0 : 0 ≤ B0 (lam ρ) (sg ρ) := sum_nonneg (fun i _ => sub_nonneg.mpr ((hI ρ).2 i).1)
    have hlen : ∀ i, 0 ≤ len (lam ρ) i :=
      fun i => sub_nonneg.mpr (((hI ρ).2 i).1.trans ((hI ρ).2 i).2)
    have hM0 : 0 ≤ ∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) :=
      sum_nonneg fun i _ => le_min (hlen i) hB0
    have hM : ∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ))
        ≤ 3 * B0 (lam ρ) (sg ρ) + ∑ i ∈ Xᶜ, len (lam ρ) i := by
      rw [← Finset.sum_add_sum_compl X]
      refine add_le_add ?_ (Finset.sum_le_sum fun i _ => min_le_left _ _)
      calc ∑ i ∈ X, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) ≤ ∑ _i ∈ X, B0 (lam ρ) (sg ρ) :=
            Finset.sum_le_sum fun i _ => min_le_right _ _
        _ = X.card * B0 (lam ρ) (sg ρ) := by simp
        _ ≤ 3 * B0 (lam ρ) (sg ρ) := by
            apply mul_le_mul_of_nonneg_right _ hB0
            exact_mod_cast hXc
    have hcast : (∑ i, ((min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ))
        = ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ) := (Int.cast_sum _ _).symm
    have hM0r : (0 : ℝ) ≤ ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ) := by
      exact_mod_cast hM0
    have hMr : ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ)
        ≤ 3 * (B0 (lam ρ) (sg ρ) : ℝ) + (eta + S) := by
      have : ((∑ i, min (len (lam ρ) i) (B0 (lam ρ) (sg ρ)) : ℤ) : ℝ)
          ≤ ((3 * B0 (lam ρ) (sg ρ) + ∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) := by exact_mod_cast hM
      rw [Int.cast_add, Int.cast_mul] at this
      have h3 : ((3 : ℤ) : ℝ) = 3 := by norm_num
      rw [h3] at this
      linarith
    have hdim := log_weyl_dimension_bound n (lam ρ) (hI ρ).1
    unfold MeanSquareTwistBound
    rw [hcast]
    by_cases hρ : ρ ∈ TT
    · rw [if_pos hρ]
      exact arithmetic_bound_at_top hC hL0 hT hb he hS hmt (Nat.cast_nonneg n) hM0r hMr (hW ρ) hdim (hbt ρ hρ)
        (hBt ρ hρ) (hdt ρ hρ)
    · rw [if_neg hρ]
      exact arithmetic_bound_off_top hC hL0 hT he hS hmt (Nat.cast_nonneg n) hM0r hMr (hW ρ) hdim
        (hBn ρ hρ) (hdn ρ hρ)
  calc logP ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT := hP
    _ ≤ ∑ ρ, ((if ρ ∈ TT then -A ρ * logT + (12 * C₀ + 2) * b' * (logT + ((n : ℝ) + 1) * L) else 0)
      + ((12 * C₀ + 2) * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + (12 * C₀ + 2) * ((n : ℝ) + 1) ^ 2 * L)) := sum_le_sum fun ρ _ => hplace ρ
    _ = _ := by
      rw [sum_add_distrib, sum_const, sum_ite_mem, univ_inter, sum_add_distrib, sum_const,
        ← sum_mul, sum_neg_distrib, card_univ, nsmul_eq_mul, nsmul_eq_mul]
      ring
end Formalism.HermitianLattices.TraceIntegrality
