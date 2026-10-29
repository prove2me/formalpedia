-- Prove2me | solution 1 for EFXGenVal.TwoVal.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T02:51:57.74547+00:00
-- url     : https://prove2.me/submissions/e600ba00-78ce-4427-8e3b-c87ae32756fc

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting
import Theorems.Thm_EFXGenVal_TwoVal_lemma_18
import Theorems.Thm_EFXGenVal_TwoVal_complete_of_theorem_14
import Theorems.Thm_EFXGenVal_TwoVal_theorem_14

/-!
Mahara, arXiv:2107.09901v2, Theorem 1 from Theorem 14: with one agent give it every item.
Otherwise split the agents into two nonempty classes `A`, `Aᶜ` with valuations `wa`, `wb`
(if all agents share one valuation, take `A = {0}` and `wa = wb`). Perturb by a small `ε`
(Appendix A): `lemma_18` gives non-degeneracy and that EFX for the perturbed profile is EFX for
the original one; the perturbed profile is still normalized, monotone and two-class, so
`complete_of_theorem_14` fed with `theorem_14` yields a complete EFX allocation for it.
-/

set_option autoImplicit false

theorem pv5dd_pos_lb (F : Finset ℝ) (hF : ∀ x ∈ F, 0 < x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F, δ ≤ x := by
  rcases F.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · exact ⟨F.min' h, hF _ (F.min'_mem h), fun x hx => F.min'_le x hx⟩

open LittleCharity.EFX EFXGenVal.TwoVal in
theorem pv5dd_two_class {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v)
    (wa wb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = wa) (hB : ∀ i ∉ A, v i = wb)
    (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty) :
    ∃ X : Fin n → Finset (Fin m), IsPartialAllocation X ∧ pool X = ∅ ∧ IsEFX v X := by
  classical
  set F : Finset ℝ :=
    ((Finset.univ : Finset (Fin n × Finset (Fin m) × Finset (Fin m))).filter
      (fun p => v p.1 p.2.1 ≠ v p.1 p.2.2)).image
      (fun p => |v p.1 p.2.1 - v p.1 p.2.2|) with hF
  have hFpos : ∀ x ∈ F, 0 < x := by
    intro x hx
    rw [hF, Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [Finset.mem_filter] at hp
    exact abs_pos.mpr (sub_ne_zero.mpr hp.2)
  obtain ⟨δ, hδ0, hδF⟩ := pv5dd_pos_lb F hFpos
  set ε : ℝ := δ / 2 ^ (m + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hδ : ∀ i S T, v i S ≠ v i T → ε * 2 ^ m < |v i S - v i T| := by
    intro i S T hST
    have hmem : |v i S - v i T| ∈ F := by
      rw [hF, Finset.mem_image]
      exact ⟨(i, S, T), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST⟩, rfl⟩
    have h1 := hδF _ hmem
    have h2 : ε * 2 ^ m = δ / 2 := by
      rw [hε, pow_succ]; field_simp
    rw [h2]; linarith
  obtain ⟨_, hnd, hback⟩ := lemma_18 v hnorm hmono ε hε0 hδ
  set v' := perturb v ε with hv'
  have hnorm' : IsNormalized v' := by
    intro i; simp [hv', perturb, hnorm i]
  have hmono' : IsMonotoneVal v' := by
    intro i S T hST
    simp only [hv', perturb]
    have h1 := hmono i S T hST
    have h2 : ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) ≤ ∑ j ∈ T, (2 : ℝ) ^ (j : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 hε0.le
    linarith
  set wa' : Finset (Fin m) → ℝ := fun S => wa S + ε * ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) with hwa'
  set wb' : Finset (Fin m) → ℝ := fun S => wb S + ε * ∑ j ∈ S, (2 : ℝ) ^ (j : ℕ) with hwb'
  have hA' : ∀ i ∈ A, v' i = wa' := by
    intro i hi; funext S; simp only [hv', perturb, hwa', hA i hi]
  have hB' : ∀ i ∉ A, v' i = wb' := by
    intro i hi; funext S; simp only [hv', perturb, hwb', hB i hi]
  obtain ⟨X, hX1, hX2, hX3⟩ := complete_of_theorem_14 v' hnorm' hmono' hnd wa' wb' A hA' hB'
    hAne hBne (fun X hX hp he =>
      theorem_14 v' hnorm' hmono' hnd wa' wb' A hA' hB' hAne hBne X hX hp he)
  exact ⟨X, hX1, hX2, hback X hX3⟩

open LittleCharity.EFX in
theorem solution {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v)
    (va vb : Finset (Fin m) → ℝ) (htype : ∀ i, v i = va ∨ v i = vb) :
    ∃ X : Fin n → Finset (Fin m), IsPartialAllocation X ∧ pool X = ∅ ∧ IsEFX v X := by
  classical
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · -- at least two agents
    set A : Finset (Fin n) := Finset.univ.filter (fun i => v i = va) with hAdef
    by_cases hsplit : A.Nonempty ∧ Aᶜ.Nonempty
    · refine pv5dd_two_class v hnorm hmono va vb A ?_ ?_ hsplit.1 hsplit.2
      · intro i hi; exact (Finset.mem_filter.mp hi).2
      · intro i hi
        rcases htype i with h | h
        · exact absurd (show i ∈ A from Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩) hi
        · exact h
    · -- all agents share one valuation
      have hall : ∀ i, v i = v ⟨0, hn⟩ := by
        have key : (∀ i, v i = va) ∨ (∀ i, v i = vb) := by
          by_cases hAn : A.Nonempty
          · have hBe : ¬ Aᶜ.Nonempty := fun h => hsplit ⟨hAn, h⟩
            left; intro i
            by_contra hi
            exact hBe ⟨i, by simp [hAdef, hi]⟩
          · right; intro i
            rcases htype i with h | h
            · exact absurd (show A.Nonempty from ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩) hAn
            · exact h
        rcases key with h | h <;> intro i <;> rw [h i, h ⟨0, hn⟩]
      refine pv5dd_two_class v hnorm hmono (v ⟨0, hn⟩) (v ⟨0, hn⟩) {⟨0, hn⟩}
        (fun i _ => hall i) (fun i _ => hall i) (Finset.singleton_nonempty _) ?_
      refine ⟨⟨1, h2⟩, ?_⟩
      simp
  · -- exactly one agent: it receives every item
    have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨fun _ => Finset.univ, ?_, ?_, ?_⟩
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
    · simp [pool]
    · intro i j g _
      exact hmono i _ _ (Finset.erase_subset _ _)
