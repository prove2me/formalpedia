-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.second_zeta_mean_of_top_thin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:47.081855+00:00
-- url     : https://prove2.me/submissions/38bea387-c7db-4b95-b8e1-6708ceb5ae6a

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
private lemma mean_mono' {σ : Type} [Fintype σ] (F G : σ → ℝ) (h : ∀ s, F s ≤ G s) :
    mean F ≤ mean G := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => h s) (Nat.cast_nonneg _)
private lemma mean_add_eq {σ : Type} [Fintype σ] (F G : σ → ℝ) :
    mean (fun s => F s + G s) = mean F + mean G := by
  unfold mean; rw [Finset.sum_add_distrib, add_div]
private lemma mean_finset_sum_comm {σ J : Type} [Fintype σ] [Fintype J] (F : J → σ → ℝ) :
    mean (fun s => ∑ j, F j s) = ∑ j, mean (F j) := by
  unfold mean; rw [Finset.sum_comm, Finset.sum_div]
private lemma mean_const_eq {σ : Type} [Fintype σ] [Nonempty σ] (c : ℝ) :
    mean (fun _ : σ => c) = c := by
  unfold mean
  have hc : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
private lemma mean_place_term_comm {σ : Type} [Fintype σ] [Nonempty σ] {N : ℕ} (nu : Fin N → ℕ)
    (x : σ → ℝ) : mean (fun s => placeTerm nu (x s)) = placeTerm nu (mean x) := by
  have hc : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold placeTerm mean
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution (ht : LargestPlaceHookBound) (hth : ThinPlaceHookBound) : MeanLogNormBound := by
  intro C₀ hC
  obtain ⟨Ct, hCt⟩ := ht C₀ hC
  obtain ⟨Cn, hCn⟩ := hth C₀ hC
  refine ⟨|Ct| + |Cn| + 2 * C₀, ?_⟩
  intro ι σ _ _ _ _ TT T2 R N m nu A w a b' L logT logg logOm logOms logTh logK hdis hRN hL hla hb1
    hba hNL hT0 hg0 hsqm hanti htop hthin hper hOm hTh hK
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hb0 : (0:ℝ) ≤ b' := by linarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg _
  have hRN' : (R:ℝ) + 1 ≤ N := by exact_mod_cast hRN
  have hRb : (R:ℝ) + 1 ≤ b' := by nlinarith
  have hlb : Real.log b' ≤ L := le_trans (Real.log_le_log (by linarith) hba) hla
  set f : ℝ := (Fintype.card ι : ℝ) with hf
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  set G : ℝ := (N:ℝ) * b' * L with hG
  have hG0 : 0 ≤ G := by positivity
  have hRG : ((R:ℝ) + 1) * b' * L ≤ G := by rw [hG]; gcongr
  have hRG0 : 0 ≤ ((R:ℝ) + 1) * b' * L := by positivity
  have hplace : ∀ τ, placeTerm (nu τ) logOm ≤ (if τ ∈ TT then topTerm (A τ) logOm else 0)
      + (if τ ∈ T2 then placeTerm (nu τ) logOm else 0) + (|Ct| + |Cn|) * G := by
    intro τ
    have hg1 : 0 ≤ |Ct| * G := by positivity
    have hg2 : 0 ≤ |Cn| * G := by positivity
    by_cases h1 : τ ∈ TT
    · have h2 : τ ∉ T2 := Finset.disjoint_left.1 hdis h1
      rw [if_pos h1, if_neg h2]
      obtain ⟨p1, p2, p3, p4, p5⟩ := htop τ h1
      have := hCt R (nu τ) (A τ) (w τ) a b' L logOm (hanti τ) p3 p4 p5 p1 p2 hb1 hba hL hla hRb hOm
      have h3 := (abs_le.1 this).2
      have h4 : Ct * ((R:ℝ) + 1) * b' * L ≤ |Ct| * G := by
        calc Ct * ((R:ℝ) + 1) * b' * L = Ct * (((R:ℝ) + 1) * b' * L) := by ring
          _ ≤ |Ct| * G := by gcongr; exact le_abs_self _
      linarith
    · by_cases h2 : τ ∈ T2
      · rw [if_neg h1, if_pos h2]; linarith
      · rw [if_neg h1, if_neg h2]
        have := hCn R (nu τ) b' L logOm (hanti τ) (hthin τ h1 h2) hb1 hL hlb hRb hOm
        have h3 := (abs_le.1 this).2
        have h4 : Cn * ((R:ℝ) + 1) * b' * L ≤ |Cn| * G := by
          calc Cn * ((R:ℝ) + 1) * b' * L = Cn * (((R:ℝ) + 1) * b' * L) := by ring
            _ ≤ |Cn| * G := by gcongr; exact le_abs_self _
        linarith
  have hsum : ∑ τ, placeTerm (nu τ) logOm ≤ ∑ τ ∈ TT, topTerm (A τ) logOm
      + ∑ τ ∈ T2, placeTerm (nu τ) logOm + f * ((|Ct| + |Cn|) * G) := by
    calc ∑ τ, placeTerm (nu τ) logOm ≤ ∑ τ, ((if τ ∈ TT then topTerm (A τ) logOm else 0)
      + (if τ ∈ T2 then placeTerm (nu τ) logOm else 0) + (|Ct| + |Cn|) * G) :=
          Finset.sum_le_sum fun τ _ => hplace τ
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.univ_inter, Finset.univ_inter]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]
  have hmean : mean logK ≤ ∑ τ, placeTerm (nu τ) logOm + mean logTh
      + C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) := by
    calc mean logK ≤ mean (fun s => (∑ τ, placeTerm (nu τ) (logOms τ s) + logTh s)
        + C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) := mean_mono' _ _ hK
      _ = _ := by
        rw [mean_add_eq, mean_add_eq, mean_finset_sum_comm, mean_const_eq]
        simp only [mean_place_term_comm, hper]
  have e1 : mean logTh ≤ C₀ * f * G := by
    refine le_trans hTh ?_
    have : (N:ℝ) ^ 2 * L ≤ G := by
      rw [hG]
      have h1 : (N:ℝ) ^ 2 * L ≤ N * b' := by nlinarith
      have h2 : (N:ℝ) * b' ≤ N * b' * L := by nlinarith [mul_nonneg hN0 hb0]
      linarith
    calc C₀ * f * (N:ℝ) ^ 2 * L = C₀ * f * ((N:ℝ) ^ 2 * L) := by ring
      _ ≤ _ := by gcongr
  have e2 : C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ C₀ * f * G := by
    calc C₀ * f * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)
        = C₀ * f * ((m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) := by ring
      _ ≤ _ := by gcongr
  have hfin : (|Ct| + |Cn| + 2 * C₀) * f * N * b' * L
      = f * ((|Ct| + |Cn|) * G) + C₀ * f * G + C₀ * f * G := by rw [hG]; ring
  rw [hfin]
  linarith
end Formalism.HermitianLattices.TraceIntegrality
