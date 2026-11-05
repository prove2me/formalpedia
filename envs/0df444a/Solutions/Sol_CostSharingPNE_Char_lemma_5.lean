-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:23:50.541179+00:00
-- url     : https://prove2.me/submissions/97fcab16-5251-48cd-87f3-29c3f454e5f9

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis

open CostSharingPNE.Char

namespace CSPLemma5Aux

variable {n : ℕ}

/-- Möbius inversion on the Boolean lattice: `W(S) = ∑_{T ⊆ S} q^W_T`. -/
lemma sum_mobius (S : Finset (Fin n)) : ∀ W : Welfare n, ∑ T ∈ S.powerset, mobius W T = W S := by
  induction S using Finset.induction_on with
  | empty => intro W; simp [mobius]
  | insert a S ha ih =>
    intro W
    rw [Finset.sum_powerset_insert ha]
    have key : ∀ T ∈ S.powerset, mobius W (insert a T) =
        - mobius W T + mobius (fun R => W (insert a R)) T := by
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      unfold mobius
      rw [Finset.sum_powerset_insert haT, Finset.card_insert_of_notMem haT, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro R hR
        have hRT := Finset.card_le_card (Finset.mem_powerset.mp hR)
        rw [show T.card + 1 - R.card = (T.card - R.card) + 1 by omega, pow_succ]
        ring
      · apply Finset.sum_congr rfl
        intro R hR
        have haR : a ∉ R := fun h => haT (Finset.mem_powerset.mp hR h)
        rw [Finset.card_insert_of_notMem haR]
        congr 2
        omega
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_neg_distrib, ih W,
      ih (fun R => W (insert a R))]
    ring

/-- (14): `W(T) = ∑_{T' ∈ 𝒯(T)} q_{T'}` when `W(∅) = 0`. -/
lemma W_eq_sum_coalitionsIn (W : Welfare n) (h0 : W ∅ = 0) (T : Finset (Fin n)) :
    W T = ∑ T' ∈ coalitionsIn W T, mobius W T' := by
  rw [← sum_mobius T W]
  symm
  apply Finset.sum_subset
  · intro T' hT'
    unfold coalitionsIn at hT'
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hT').2
  · intro T' hT' hn
    unfold coalitionsIn coalitions at hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hn
    by_cases hne : T'.Nonempty
    · by_contra hq
      exact hn ⟨hne, hq⟩ (Finset.mem_powerset.mp hT')
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [mobius, h0]

end CSPLemma5Aux

open CSPLemma5Aux in
theorem solution (n : ℕ) (hn : 1 < n) (W : Welfare n) (g : Rule n)
    (hbb : IsBudgetBalanced g W) (h0 : ∀ i S, i ∉ S → g i S = 0) :
    ∀ T ∈ coalitions W, ∀ S : Finset (Fin n),
      ∑ i ∈ S, basisRule g W T i S = unanimity T S := by
  have hW0 : W ∅ = 0 := by have := hbb ∅; simpa using this.symm
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hT S
    have hq : mobius W T ≠ 0 := by
      unfold coalitions at hT
      exact (Finset.mem_filter.mp hT).2.2
    have hTin : T ∈ coalitionsIn W T := by
      unfold coalitionsIn
      exact Finset.mem_filter.mpr ⟨hT, Finset.Subset.refl T⟩
    have hunf : ∀ i, basisRule g W T i S = if T ⊆ S then
        (1 / mobius W T) * (g i T - ∑ T' ∈ ((coalitionsIn W T).erase T).attach,
          mobius W T'.1 * basisRule g W T'.1 i S) else 0 := by
      intro i; rw [basisRule]
    simp_rw [hunf]
    unfold unanimity
    by_cases hTS : T ⊆ S
    · simp only [if_pos hTS]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_comm]
      have hsub : ∀ T' ∈ ((coalitionsIn W T).erase T).attach,
          ∑ i ∈ S, mobius W T'.1 * basisRule g W T'.1 i S = mobius W T'.1 := by
        intro T' _
        have h := T'.2
        rw [Finset.mem_erase] at h
        unfold coalitionsIn at h
        rw [Finset.mem_filter] at h
        have hss : T'.1 ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨h.2.2, h.1⟩
        rw [← Finset.mul_sum, ih T'.1 hss h.2.1 S, unanimity, if_pos (h.2.2.trans hTS), mul_one]
      rw [Finset.sum_congr rfl hsub, Finset.sum_attach (s := (coalitionsIn W T).erase T)
        (f := fun T' => mobius W T')]
      have hgT : ∑ i ∈ S, g i T = W T := by
        rw [← hbb T]
        symm
        apply Finset.sum_subset hTS
        intro i _ hi
        exact h0 i T hi
      rw [hgT, Finset.sum_erase_eq_sub hTin, ← W_eq_sum_coalitionsIn W hW0 T]
      field_simp
      ring
    · simp [if_neg hTS]
