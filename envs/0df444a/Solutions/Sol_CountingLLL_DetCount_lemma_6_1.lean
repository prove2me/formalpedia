-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:33:11.21258+00:00
-- url     : https://prove2.me/submissions/0865068e-f05d-40b9-bce0-080542990f3d

import Theorems.Thm_CountingLLL_DetCount_positive_probability_ratio_telescope
import Theorems.Thm_CountingLLL_DetCount_violation_event_tree_expansion
import Theorems.Thm_CountingLLL_DetCount_tree_event_far_independence

set_option autoImplicit false
open scoped Classical
open CountingLLL.DetCount
open CountingLLL.DetCount.CSP

private theorem z_antitone (Φ : CSP) {E F : Finset (Fin Φ.m)} (h : E ⊆ F) : Φ.Z F ≤ Φ.Z E := by
  classical
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  intro c hc
  exact hσ c (h hc)

private theorem prob_sat_pos (Φ : CSP) (E : Finset (Fin Φ.m)) (hZ : 0 < Φ.Z E) :
    0 < Φ.prob (Φ.SatAll E) := by
  change 0 < (Φ.Z E : ℝ) / (Fintype.card Φ.Config : ℝ)
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  have hc : 0 < (Fintype.card Φ.Config : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Φ.Config)
  exact div_pos (by exact_mod_cast hZ) hc

private theorem prob_nonneg (Φ : CSP) (A : Φ.Config → Prop) : 0 ≤ Φ.prob A := by
  unfold CSP.prob
  positivity

private theorem prob_mono (Φ : CSP) (A B : Φ.Config → Prop) (h : ∀ σ, A σ → B σ) :
    Φ.prob A ≤ Φ.prob B := by
  unfold CSP.prob
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro σ hσ
  have ha := (Finset.mem_filter.mp hσ).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h σ ha⟩

private theorem far_subset_erase (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    Φ.free E r T \ Φ.free1 E r T ⊆ E.erase r := by
  intro c hc
  have hf := (Finset.mem_sdiff.mp hc).1
  have hroot : r ∈ T := (Finset.mem_filter.mp hT).2.1
  have hfree := Finset.mem_sdiff.mp hf
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfree.1⟩
  intro heq
  subst c
  exact hfree.2 (Finset.mem_union.mpr (Or.inl hroot))

theorem solution (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (hpos : 0 < Φ.Z E)
    (e : (T : Finset (Fin Φ.m)) →
      Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card → Fin Φ.m)
    (he : ∀ T ∈ Φ.twoTrees E r, Function.Injective (e T) ∧
      ∀ j, e T j ∈ (E.erase r) \ (Φ.free E r T \ Φ.free1 E r T))
    (A : Φ.Config → Prop) :
    Φ.prob (fun σ => A σ ∧ ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ) /
        Φ.prob (Φ.SatAll (E.erase r)) =
      ∑ T ∈ Φ.twoTrees E r,
        (-1 : ℝ) ^ (T.card - 1) *
        Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ) *
        (∏ j : Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card,
          1 / (1 - Φ.r (Φ.prefixFam (Φ.free E r T \ Φ.free1 E r T) (e T) j) (e T j))) *
        (Φ.prob (fun σ => A σ ∧ Φ.SatAll (Φ.free E r T \ Φ.free1 E r T) σ ∧
          (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ)) /
         Φ.prob (fun σ => Φ.SatAll (Φ.free E r T \ Φ.free1 E r T) σ ∧
          (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ))) := by
  classical
  let H := E.erase r
  have hHE : H ⊆ E := Finset.erase_subset _ _
  have hHposZ : 0 < Φ.Z H := lt_of_lt_of_le hpos (z_antitone Φ hHE)
  have hHpos : 0 < Φ.prob (Φ.SatAll H) := prob_sat_pos Φ H hHposZ
  have hleft : Φ.prob (fun σ => A σ ∧ ¬ Φ.Sat r σ ∧ Φ.SatAll H σ) =
      Φ.prob (fun σ => A σ ∧ (¬ Φ.Sat r σ ∧ Φ.SatAll H σ)) := by
    congr 1
  rw [hleft, violation_event_tree_expansion Φ E r hr A, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  let N := Φ.free1 E r T
  let B := Φ.free E r T \ N
  let Q : Φ.Config → Prop := fun σ => Φ.ViolAll T σ ∧ Φ.SatAll N σ
  let U : Φ.Config → Prop := fun σ => A σ ∧ Φ.SatAll B σ ∧ Q σ
  have hBH : B ⊆ H := far_subset_erase Φ E T r hT
  have hBposZ : 0 < Φ.Z B := lt_of_lt_of_le hpos (z_antitone Φ (hBH.trans hHE))
  have hBpos : 0 < Φ.prob (Φ.SatAll B) := prob_sat_pos Φ B hBposZ
  have hNsub : N ⊆ Φ.free E r T := Finset.filter_subset _ _
  have hdecomp : N ∪ B = Φ.free E r T := Finset.union_sdiff_of_subset hNsub
  have hSat : ∀ σ, Φ.SatAll (Φ.free E r T) σ ↔ Φ.SatAll N σ ∧ Φ.SatAll B σ := by
    intro σ
    rw [← hdecomp]
    simp [CSP.SatAll, or_imp, forall_and]
  have hEvent : (fun σ => A σ ∧ (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ)) = U := by
    funext σ
    apply propext
    dsimp [U, Q]
    rw [hSat σ]
    tauto
  have hfactor : Φ.prob (fun σ => Φ.SatAll B σ ∧ Q σ) =
      Φ.prob (Φ.SatAll B) * Φ.prob Q := tree_event_far_independence Φ E T r hT
  have htelescope := positive_probability_ratio_telescope Φ B H hHposZ hBH (e T) (he T hT)
  rw [hEvent, ← htelescope]
  change ((-1 : ℝ) ^ (T.card - 1) * Φ.prob U) / Φ.prob (Φ.SatAll H) =
    (-1 : ℝ) ^ (T.card - 1) * Φ.prob Q *
      (Φ.prob (Φ.SatAll B) / Φ.prob (Φ.SatAll H)) *
      (Φ.prob U / Φ.prob (fun σ => Φ.SatAll B σ ∧ Q σ))
  rw [hfactor]
  by_cases hQ : Φ.prob Q = 0
  · have hUle : Φ.prob U ≤ Φ.prob (fun σ => Φ.SatAll B σ ∧ Q σ) :=
      prob_mono Φ U _ (fun σ h => ⟨h.2.1, h.2.2⟩)
    have hU0 : Φ.prob U = 0 := by
      apply le_antisymm _ (prob_nonneg Φ U)
      rw [hfactor, hQ, mul_zero] at hUle
      exact hUle
    simp [hU0, hQ]
  · field_simp
    <;> ring
