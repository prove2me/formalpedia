-- Prove2me | solution 1 for Formalism.GM.le_gaussR_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:38.969494+00:00
-- url     : https://prove2.me/submissions/b00c0cca-eed2-4cf6-9b45-389c33fba90e

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Theorems.Thm_Formalism_GM_gaussR_term_le
import Theorems.Thm_Formalism_GM_gaussR_attained_least
import Theorems.Thm_Formalism_GM_gaussR_pos
import Theorems.Thm_Formalism_GM_gaussR_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]
variable [IsUltrametricDist K]
namespace Formalism.GM
theorem _root_.solution (ρ : NNReal) (hρ : 0 < ρ) (P Q : K[X]) :
    gaussR ρ P * gaussR ρ Q ≤ gaussR ρ (P * Q) := by
  by_cases hP : P = 0
  · simp [hP, gaussR_zero]
  by_cases hQ : Q = 0
  · simp [hQ, gaussR_zero]
  obtain ⟨i₀, hi₀, hlt_i⟩ := gaussR_attained_least ρ P hP
  obtain ⟨j₀, hj₀, hlt_j⟩ := gaussR_attained_least ρ Q hQ
  have hgP := gaussR_pos ρ hρ P hP
  have hgQ := gaussR_pos ρ hρ Q hQ
  have hρk : 0 < ρ ^ (i₀ + j₀) := pow_pos hρ _
  have hsplit : (P * Q).coeff (i₀ + j₀) = P.coeff i₀ * Q.coeff j₀ +
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2 := by
    have hmem : ((i₀, j₀) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (i₀ + j₀) :=
      Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    rw [Polynomial.coeff_mul, Finset.add_sum_erase _ (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem]
  have hterm : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀),
      ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    intro x hx
    obtain ⟨hne, hx'⟩ := Finset.mem_erase.1 hx
    have hsum : x.1 + x.2 = i₀ + j₀ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx'
    have e : ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) =
        (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
      rw [nnnorm_mul, ← hsum, pow_add]
      ring
    rw [e]
    by_cases h1 : x.1 < i₀
    · calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ (‖P.coeff x.1‖₊ * ρ ^ x.1) * gaussR ρ Q := mul_le_mul_of_nonneg_left (gaussR_term_le ρ Q _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_right (hlt_i _ h1) hgQ
    · have h2 : x.2 < j₀ := by
        by_contra h
        exact hne (Prod.ext (by omega) (by omega))
      calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ gaussR ρ P * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := mul_le_mul_of_nonneg_right (gaussR_term_le ρ P _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_left (hlt_j _ h2) hgP
  have hsup : ((Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀)).sup
      (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) < gaussR ρ P * gaussR ρ Q :=
    (Finset.sup_lt_iff (mul_pos hgP hgQ)).2 hterm
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    refine lt_of_le_of_lt ?_ hsup
    rw [← le_div_iff₀ hρk]
    apply IsUltrametricDist.nnnorm_sum_le_of_forall_le
    intro x hx
    rw [le_div_iff₀ hρk]
    exact Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) hx
  have hmain : ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) = gaussR ρ P * gaussR ρ Q := by
    rw [nnnorm_mul, pow_add, ← hi₀, ← hj₀]
    ring
  have h' : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) := by
    rw [hmain]
    exact hrest
  have hlt := lt_of_mul_lt_mul_right h' zero_le
  have heq : ‖(P * Q).coeff (i₀ + j₀)‖₊ = ‖P.coeff i₀ * Q.coeff j₀‖₊ := by
    rw [hsplit, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hlt.ne', max_eq_left hlt.le]
  calc gaussR ρ P * gaussR ρ Q = ‖(P * Q).coeff (i₀ + j₀)‖₊ * ρ ^ (i₀ + j₀) := by rw [heq, hmain]
    _ ≤ gaussR ρ (P * Q) := gaussR_term_le ρ (P * Q) _
end Formalism.GM
