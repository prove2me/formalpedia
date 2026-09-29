-- Prove2me | solution 1 for FoundationsRL.Structured.igw_minimizes_dec
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:20:21.023836+00:00
-- url     : https://prove2.me/submissions/d8ebf0f7-d748-4273-aba7-1bf486d65b09

import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC
import Definitions.Def_FoundationsRL_Contextual_IsIGW

namespace FoundationsRL.Structured

/-- A maximizer selector on `Fin 2`. -/
noncomputable def aux_igwdec_piStar (f : Fin 2 → ℝ) : Fin 2 := if f 0 ≤ f 1 then 1 else 0

lemma aux_igwdec_piStar_spec : ∀ f : Fin 2 → ℝ, ∀ π : Fin 2, f π ≤ f (aux_igwdec_piStar f) := by
  intro f π
  unfold aux_igwdec_piStar
  fin_cases π <;> split_ifs with h <;> simp at * <;> linarith

lemma aux_igwdec_isIGW :
    Contextual.IsIGW 2 ![0, -3/2] (4 * (1/8 : ℝ)) 0 ![2/3, 1/3] where
  greedy := by
    intro π; fin_cases π <;> norm_num
  lam_spec := by
    refine ⟨3/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro π; fin_cases π <;> norm_num
  nonneg := by
    intro π; fin_cases π <;> norm_num
  sum_one := by
    rw [Fin.sum_univ_two]; norm_num

end FoundationsRL.Structured

open FoundationsRL.Structured

theorem solution : ¬ (∀ {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ f : Fin A → ℝ, ∀ π : Fin A, f π ≤ f (piStar f))
    (bstar : Fin A) (p : Fin A → ℝ) (hIGW : FoundationsRL.Contextual.IsIGW A fhat (4 * γ) bstar p),
    decGf (Set.univ : Set (Fin A → ℝ)) piStar γ fhat ≤ ((A : ℝ) - 1) / (4 * γ) ∧
    (∀ q : Fin A → ℝ, (∀ π, 0 < q π) → (∑ π, q π = 1) →
      ((A : ℝ) - 1) / (4 * γ) ≤ sSup ((fun f : Fin A → ℝ =>
          ∑ π, q π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) ''
        (Set.univ : Set (Fin A → ℝ)))) ∧
    sSup ((fun f : Fin A → ℝ =>
        ∑ π, p π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) ''
      (Set.univ : Set (Fin A → ℝ))) = ((A : ℝ) - 1) / (4 * γ)) := by
  intro h
  have h3 := (h (A := 2) ![0, -3/2] (1/8) (by norm_num) aux_igwdec_piStar
    aux_igwdec_piStar_spec 0 ![2/3, 1/3] aux_igwdec_isIGW).2.2
  set S := ((fun f : Fin 2 → ℝ =>
        ∑ π, (![2/3, 1/3] : Fin 2 → ℝ) π * (f (aux_igwdec_piStar f) - f π
          - (1/8 : ℝ) * (f π - (![0, -3/2] : Fin 2 → ℝ) π) ^ 2)) ''
      (Set.univ : Set (Fin 2 → ℝ))) with hS
  have hval : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [hval] at h3
  norm_num at h3
  by_cases hb : BddAbove S
  · have hmem : (3 : ℝ) ∈ S := by
      refine ⟨![-4, 13/2], Set.mem_univ _, ?_⟩
      have hp : aux_igwdec_piStar ![-4, 13/2] = 1 := by
        unfold aux_igwdec_piStar; norm_num
      simp only [hp, Fin.sum_univ_two]
      norm_num
    have := le_csSup hb hmem
    linarith
  · have := Real.sSup_of_not_bddAbove hb
    linarith
