-- Prove2me | solution 1 for CoverModular.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:14:34.090812+00:00
-- url     : https://prove2.me/submissions/588977c5-2635-48b3-a13a-7cdfb415ce50

import Mathlib
import Definitions.Def_CoverModular_FDPInstance_Standing
import Definitions.Def_CoverModular_FDPInstance_F

namespace Aux_Q01_CoverModular_lemma_2
open BipartiteMatchingHT.Delay CoverModular

theorem feas_zero {I J : Type} [Fintype I] [Fintype J] (c : I → ℝ) (d : J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (A : Finset (I × J)) :
    (network c d A).Feasible (fun _ _ => 0) := by
  refine ⟨fun _ _ => le_refl _, fun _ _ _ => rfl, fun i => ?_, fun j => ?_⟩
  · simp only [Finset.sum_const_zero]
    exact hc i
  · simp only [Finset.sum_const_zero]
    exact hd j

theorem bdd {I J : Type} [Fintype I] [Fintype J] (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (A : Finset (I × J)) :
    BddAbove (profit p '' {x | (network c d A).Feasible x}) := by
  refine ⟨∑ i, ∑ j, p i j * c i, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hnn, -, hsup, -⟩ := hx
  unfold profit
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hp i j)
  calc x i j ≤ ∑ j', x i j' := Finset.single_le_sum (fun j' _ => hnn i j') (Finset.mem_univ j)
    _ ≤ c i := hsup i

theorem lp_nonneg {I J : Type} [Fintype I] [Fintype J] (c : I → ℝ) (d : J → ℝ)
    (p : I → J → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (A : Finset (I × J)) : 0 ≤ lpValue c d p A := by
  unfold lpValue
  apply le_csSup (bdd c d p hp A)
  exact ⟨fun _ _ => 0, feas_zero c d hc hd A, by simp [profit]⟩

theorem lp_mono {I J : Type} [Fintype I] [Fintype J] (c : I → ℝ) (d : J → ℝ)
    (p : I → J → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (A B : Finset (I × J)) (hAB : A ⊆ B) : lpValue c d p A ≤ lpValue c d p B := by
  unfold lpValue
  have hne : (profit p '' {x | (network c d A).Feasible x}).Nonempty :=
    ⟨_, ⟨fun _ _ => 0, feas_zero c d hc hd A, rfl⟩⟩
  apply csSup_le_csSup (bdd c d p hp B) hne
  apply Set.image_mono
  intro x hx
  exact ⟨hx.1, fun i j hij => hx.2.1 i j (fun h => hij (hAB h)), hx.2.2.1, hx.2.2.2⟩

end Aux_Q01_CoverModular_lemma_2

open CoverModular in
theorem solution {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I]
    [DecidableEq J] (inst : FDPInstance I J Ω) (hinst : inst.Standing) :
    (∀ A : Finset (I × J), 0 ≤ inst.F A) ∧
      ∀ A B : Finset (I × J), A ⊆ B → inst.F A ≤ inst.F B := by
  obtain ⟨hμ, hc, hd, hp⟩ := hinst
  constructor
  · intro A
    unfold FDPInstance.F
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω)
      (Aux_Q01_CoverModular_lemma_2.lp_nonneg _ _ _ (fun i => hc i ω) (fun j => hd j ω) hp A))
  · intro A B hAB
    unfold FDPInstance.F
    exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left
      (Aux_Q01_CoverModular_lemma_2.lp_mono _ _ _ (fun i => hc i ω) (fun j => hd j ω) hp A B hAB)
      (hμ ω))
