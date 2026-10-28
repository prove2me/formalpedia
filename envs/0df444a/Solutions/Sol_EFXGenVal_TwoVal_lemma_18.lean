-- Prove2me | solution 1 for EFXGenVal.TwoVal.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:00:54.626971+00:00
-- url     : https://prove2.me/submissions/3fd0547b-6bb8-4a40-8e28-77c5c82359b0

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

open LittleCharity.EFX

namespace Aux_EFX18

lemma s_nonneg {m : ℕ} (S : Finset (Fin m)) : 0 ≤ ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) :=
  Finset.sum_nonneg (fun _ _ => by positivity)

lemma s_lt {m : ℕ} (S : Finset (Fin m)) : ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) < 2 ^ m := by
  have h1 : ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) ≤ ∑ j : Fin m, (2 : ℝ) ^ (j : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
  have h2 : ∑ j : Fin m, (2 : ℝ) ^ (j : ℕ) = 2 ^ m - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (2 : ℝ) ^ k), geom_sum_eq (by norm_num)]
    norm_num
  linarith

lemma s_inj {m : ℕ} (S T : Finset (Fin m))
    (h : ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) = ∑ j ∈ T, (2 : ℝ) ^ (j : ℕ)) : S = T := by
  have hS : ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) = ((∑ k ∈ S.map Fin.valEmbedding, 2 ^ k : ℕ) : ℝ) := by
    rw [Finset.sum_map]; push_cast; rfl
  have hT : ∑ j ∈ T, (2 : ℝ) ^ (j : ℕ) = ((∑ k ∈ T.map Fin.valEmbedding, 2 ^ k : ℕ) : ℝ) := by
    rw [Finset.sum_map]; push_cast; rfl
  rw [hS, hT] at h
  have h' := Nat.cast_injective h
  have := Finset.geomSum_injective (le_refl 2) h'
  exact Finset.map_injective Fin.valEmbedding this

end Aux_EFX18

open EFXGenVal.TwoVal in
theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v)
    (ε : ℝ) (hε : 0 < ε)
    (hδ : ∀ i S T, v i S ≠ v i T → ε * 2 ^ m < |v i S - v i T|) :
    (∀ i S T, v i T < v i S → perturb v ε i T < perturb v ε i S) ∧
      IsNonDegenerate (perturb v ε) ∧
      (∀ X : Fin n → Finset (Fin m), IsEFX (perturb v ε) X → IsEFX v X) := by
  have part1 : ∀ i S T, v i T < v i S → perturb v ε i T < perturb v ε i S := by
    intro i S T hlt
    have h := hδ i S T (ne_of_gt hlt)
    rw [abs_of_pos (by linarith)] at h
    unfold perturb
    have a1 := Aux_EFX18.s_nonneg S
    have a2 := Aux_EFX18.s_lt T
    have : ε * ∑ j ∈ T, (2 : ℝ) ^ (j : ℕ) < ε * 2 ^ m := mul_lt_mul_of_pos_left a2 hε
    have : 0 ≤ ε * ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) := mul_nonneg hε.le a1
    linarith
  refine ⟨part1, ?_, ?_⟩
  · intro i S T hST
    by_cases hv : v i S = v i T
    · intro heq
      unfold perturb at heq
      rw [hv] at heq
      have h2 : ε * ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) = ε * ∑ j ∈ T, (2 : ℝ) ^ (j : ℕ) := by linarith
      exact hST (Aux_EFX18.s_inj S T (mul_left_cancel₀ hε.ne' h2))
    · rcases lt_or_gt_of_ne hv with h | h
      · exact ne_of_lt (part1 i T S h)
      · exact ne_of_gt (part1 i S T h)
  · intro X hX i j g hg
    by_contra hc
    push_neg at hc
    have := part1 i _ _ hc
    have := hX i j g hg
    linarith
