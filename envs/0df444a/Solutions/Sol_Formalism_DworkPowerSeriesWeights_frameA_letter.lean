-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frameA_letter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:00.826891+00:00
-- url     : https://prove2.me/submissions/ecf6cd70-8d76-47a7-bf04-52c00ca242f6

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementK
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_inv_entry_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] (J N0 : ℕ)
    (lam : Fin J → Fin N0 → K) (y : Fin N0 → Fin N0 → K) (hlam : ∀ i a, ‖lam i a‖ ≤ 1)
    (hy : ∀ k a, ‖y k a‖ ≤ 1) (e : Fin J → Fin N0) (he : Function.Injective e)
    (top : Fin N0 → Prop) [DecidablePred top] (htop : ∀ i, ¬ top (e i))
    (hdet : ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1) :
    ∃ (x T : Fin N0 → Fin N0 → K), (∀ k a, ‖x k a‖ ≤ 1) ∧ (∀ i k, ‖T i k‖ ≤ 1) ∧
      (∀ k a, top k → x k a = y k a) ∧
      (∀ i a, ¬ top i → y i a = ∑ k, (if top k then 0 else T i k) * x k a) ∧
      (∀ i k, ¬ top k → k ≠ e i → ∑ a, lam i a * x k a = 0) := by
  classical
  set A : Matrix (Fin J) (Fin J) K := Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a
    with hA
  let c : Fin N0 → Fin J → K := fun k i => ∑ a, lam i a * y k a
  have hc : ∀ k i, ‖c k i‖ ≤ 1 := fun k i =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => by
      rw [norm_mul]; exact mul_le_one₀ (hlam i a) (norm_nonneg _) (hy k a))
  have hAc : ∀ i i', A i i' = c (e i') i := fun _ _ => rfl
  have hAint : ∀ i i', ‖A i i'‖ ≤ 1 := fun i i' => hc _ _
  have hAinv : ∀ i i', ‖A⁻¹ i i'‖ ≤ 1 := norm_inv_entry_le_one A hAint hdet
  have hne : A.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  let z : Fin J → Fin N0 → K := fun i' a => ∑ i'', A⁻¹ i'' i' * y (e i'') a
  have hz : ∀ i a, ‖z i a‖ ≤ 1 := fun i a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i'' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hAinv _ _) (norm_nonneg _) (hy _ _))
  have hcz : ∀ k a, ‖∑ i', c k i' * z i' a‖ ≤ 1 := fun k a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hc _ _) (norm_nonneg _) (hz _ _))

  have hlz : ∀ i i', ∑ a, lam i a * z i' a = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : ∑ a, lam i a * z i' a = ∑ i'', A i i'' * A⁻¹ i'' i' := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i'' _ => ?_)
      rw [hAc]
      simp only [c, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [h1, ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hunit, Matrix.one_apply]

  have hzy : ∀ i'' a, ∑ i', c (e i'') i' * z i' a = y (e i'') a := by
    intro i'' a
    have h1 : ∑ i', c (e i'') i' * z i' a = ∑ m, (∑ i', A⁻¹ m i' * A i' i'') * y (e m) a := by
      simp only [z, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i' _ => ?_))
      rw [hAc]; ring
    rw [h1]
    simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]
    simp
  let x : Fin N0 → Fin N0 → K := fun k a =>
    if top k then y k a else if h : ∃ i, e i = k then z h.choose a
      else y k a - ∑ i', c k i' * z i' a
  let T : Fin N0 → Fin N0 → K := fun i k =>
    (if (∃ i', e i' = i) then 0 else if k = i then 1 else 0) + ∑ i', if k = e i' then c i i' else 0
  have hxe : ∀ i a, x (e i) a = z i a := by
    intro i a
    have hex : ∃ i', e i' = e i := ⟨i, rfl⟩
    have hch : hex.choose = i := he hex.choose_spec
    simp only [x]
    rw [if_neg (htop i), dif_pos hex, hch]
  have hxn : ∀ k a, ¬ top k → (¬ ∃ i, e i = k) → x k a = y k a - ∑ i', c k i' * z i' a := by
    intro k a h1 h2
    simp only [x]
    rw [if_neg h1, dif_neg h2]
  have hsumT : ∀ i k, (∑ i', if k = e i' then c i i' else 0) = 0 ∨
      ∃ i', (∑ i', if k = e i' then c i i' else 0) = c i i' := by
    intro i k
    by_cases h : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h
      right
      refine ⟨i0, ?_⟩
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (he h).symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · left
      refine Finset.sum_eq_zero (fun i' _ => ?_)
      rw [if_neg (fun hk => h ⟨i', hk.symm⟩)]
  refine ⟨x, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro k a
    by_cases h1 : top k
    · simp only [x]; rw [if_pos h1]; exact hy _ _
    · by_cases h2 : ∃ i, e i = k
      · obtain ⟨i, rfl⟩ := h2
        rw [hxe]; exact hz _ _
      · rw [hxn k a h1 h2, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ _) ?_)
        rw [norm_neg]; exact hcz _ _
  · intro i k
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · rcases hsumT i k with h | ⟨i', h⟩
      · rw [h]; simp
      · rw [h]; exact hc _ _
  · intro k a h1
    simp only [x]; rw [if_pos h1]
  · intro i a hi
    have hT0 : ∀ k, (if top k then 0 else T i k) = T i k := by
      intro k
      split_ifs with hk
      · symm
        have h1 : k ≠ i := fun h => hi (h ▸ hk)
        have h2 : (∑ i', if k = e i' then c i i' else 0) = 0 :=
          Finset.sum_eq_zero (fun i' _ => by
            rw [if_neg (fun h : k = e i' => htop i' (h ▸ hk))])
        simp only [T]
        rw [h2, if_neg h1]
        simp
      · rfl
    simp only [hT0]
    have hsecond : ∑ k, (∑ i', if k = e i' then c i i' else 0) * x k a = ∑ i', c i i' * z i' a := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      rw [Finset.sum_eq_single (e i')]
      · rw [if_pos rfl, hxe]
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [T, add_mul, Finset.sum_add_distrib]
    rw [hsecond]
    by_cases h2 : ∃ i', e i' = i
    · simp only [if_pos h2, zero_mul, Finset.sum_const_zero, zero_add]
      obtain ⟨i0, rfl⟩ := h2
      exact (hzy i0 a).symm
    · simp only [if_neg h2]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul, hxn i a hi h2]; ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  · intro i k hk hne'
    by_cases h2 : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h2
      simp only [hxe]
      rw [hlz, if_neg (fun h : i = i0 => hne' (h ▸ rfl))]
    · simp only [hxn k _ hk h2, mul_sub, Finset.sum_sub_distrib]
      have h3 : ∑ a, lam i a * ∑ i', c k i' * z i' a = ∑ i', c k i' * ∑ a, lam i a * z i' a := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun a _ => by ring))
      rw [h3]
      simp only [hlz]
      simp [c]
end Formalism.DworkPowerSeriesWeights
