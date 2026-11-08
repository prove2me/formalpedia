-- Prove2me | solution 1 for CoverModular.dual_objective_eq_two_f
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:48:55.298093+00:00
-- url     : https://prove2.me/submissions/e4d7a691-c256-44b5-8c4e-ba9b7029e1f7

import Mathlib
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_alphaBar

open BipartiteMatchingHT.Delay

open CoverModular in
theorem solution {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, p i j ≤ P)
    (S : Finset (I × J)) (x : I → J → ℝ) (hx : IsOptimal c d p S x) :
    ∑ i, c i * alphaBar c p P x i + ∑ j, d j * betaBar d p P x j = 2 * lpValue c d p S := by
  obtain ⟨hF, hopt⟩ := hx
  have hF' := hF
  obtain ⟨hnn, _, hrow, hcol⟩ := hF'
  have h1 : ∀ i, c i * alphaBar c p P x i = ∑ j, p i j * x i j := by
    intro i
    unfold alphaBar
    by_cases h : 0 < c i
    · rw [if_pos h]; field_simp
    · rw [if_neg h]
      have hc0 : c i = 0 := le_antisymm (not_lt.mp h) (hc i)
      have hr : ∑ j, x i j ≤ 0 := by simpa [network, hc0] using hrow i
      have hz : ∀ j, x i j = 0 := by
        intro j
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).mp
          (le_antisymm hr (Finset.sum_nonneg (fun j _ => hnn i j))) j (Finset.mem_univ _)
        exact this
      simp [hc0, hz]
  have h2 : ∀ j, d j * betaBar d p P x j = ∑ i, p i j * x i j := by
    intro j
    unfold betaBar
    by_cases h : 0 < d j
    · rw [if_pos h]; field_simp
    · rw [if_neg h]
      have hd0 : d j = 0 := le_antisymm (not_lt.mp h) (hd j)
      have hr : ∑ i, x i j ≤ 0 := by simpa [network, hd0] using hcol j
      have hz : ∀ i, x i j = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i j)).mp
          (le_antisymm hr (Finset.sum_nonneg (fun i _ => hnn i j))) i (Finset.mem_univ _)
      simp [hd0, hz]
  have hlp : lpValue c d p S = profit p x := by
    unfold lpValue
    apply IsGreatest.csSup_eq
    refine ⟨⟨x, hF, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hopt y hy
  rw [hlp, Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun j _ => h2 j),
    Finset.sum_comm (f := fun j i => p i j * x i j)]
  unfold profit
  ring
