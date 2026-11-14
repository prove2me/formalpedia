-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:33:10.556197+00:00
-- url     : https://prove2.me/submissions/950d05c9-70a7-4ab5-82e0-7ce4f51a1922

import Theorems.Thm_CountingLLL_DetCount_condition11_partition_positive
import Theorems.Thm_CountingLLL_DetCount_marginal_expansion_eq11
import Theorems.Thm_CountingLLL_DetCount_conditional_probability_free1
import Theorems.Thm_CountingLLL_DetCount_free_near_far_independence
import Theorems.Thm_CountingLLL_DetCount_general_probability_ratio_telescope

set_option autoImplicit false
open scoped Classical
open CountingLLL.DetCount
open CountingLLL.DetCount.CSP

private theorem prob_sat_pos (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) :
    0 < Φ.prob (Φ.SatAll E) := by
  change 0 < (Φ.Z E : ℝ) / (Fintype.card Φ.Config : ℝ)
  have hz := condition11_partition_positive Φ hΦ E
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  have hc : 0 < (Fintype.card Φ.Config : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Φ.Config)
  exact div_pos (by exact_mod_cast hz) hc

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

/-- Lemma 5.1, using the exact distant-free base and its complement in the root-deleted family. -/
theorem solution (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E)
    (e : (T : Finset (Fin Φ.m)) →
      Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card → Fin Φ.m)
    (he : ∀ T ∈ Φ.twoTrees E r, Function.Injective (e T) ∧
      ∀ j, e T j ∈ (E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)) :
    Φ.r E r = ∑ T ∈ Φ.twoTrees E r, (-1 : ℝ) ^ (T.card - 1) *
      Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ) *
      ∏ j : Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card,
        1 / (1 - Φ.r (Φ.prefixFam (Φ.free E r T \ Φ.free1 E r T) (e T) j) (e T j)) := by
  rw [marginal_expansion_eq11 Φ hΦ E r hr]
  apply Finset.sum_congr rfl
  intro T hT
  let N := Φ.free1 E r T
  let B := Φ.free E r T \ N
  let H := E.erase r
  have hFpos : 0 < Φ.prob (Φ.SatAll (Φ.free E r T)) := prob_sat_pos Φ hΦ _
  have hNpos : 0 < Φ.prob (Φ.SatAll N) := prob_sat_pos Φ hΦ _
  have hHpos : 0 < Φ.prob (Φ.SatAll H) := prob_sat_pos Φ hΦ _
  have hcoeff := conditional_probability_free1 Φ E T r hT hFpos
  have hfactor := free_near_far_independence Φ E T r hT
  have htelescope := general_probability_ratio_telescope Φ hΦ B H (far_subset_erase Φ E T r hT) (e T) (he T hT)
  rw [← htelescope, hcoeff]
  change (-1 : ℝ) ^ (T.card - 1) *
      (Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll N σ) / Φ.prob (Φ.SatAll N)) *
      (Φ.prob (Φ.SatAll (Φ.free E r T)) / Φ.prob (Φ.SatAll H)) =
    (-1 : ℝ) ^ (T.card - 1) *
      Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll N σ) *
      (Φ.prob (Φ.SatAll B) / Φ.prob (Φ.SatAll H))
  rw [hfactor]
  field_simp
  rfl
