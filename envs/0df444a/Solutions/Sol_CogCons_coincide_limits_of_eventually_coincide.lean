-- Prove2me | solution 1 for CogCons.coincide_limits_of_eventually_coincide
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:11:14.02126+00:00
-- url     : https://prove2.me/submissions/e50866cd-d921-4b06-8242-c05a5826aa26

import Definitions.Def_CogCons_similarity_distance

open CogCons CogCons.CognitiveSimilarityDistance

theorem solution {C : Type*} (D : CognitiveSimilarityDistance C)
    (s t : ℕ → C) (k : ℕ) (hst : ∀ i ≥ k, D.coincide (s i) (t i))
    (x y : C) (hs : D.ConvergesTo s x) (ht : D.ConvergesTo t y) :
    D.coincide x y := by
  apply (D.Cog_eq_zero_iff x y).mp
  by_contra hn
  have hb := D.Cog_mem_Icc x y
  have hp : 0 < D.Cog x y := lt_of_le_of_ne hb.1 (Ne.symm hn)
  have he : D.Cog x y / 3 ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith [hb.2]
  obtain ⟨m, hm⟩ := hs _ he
  obtain ⟨n, hn⟩ := ht _ he
  let N := max k (max m n)
  have hk : k ≤ N := le_max_left _ _
  have hmN : m ≤ N := (le_max_left m n).trans (le_max_right _ _)
  have hnN : n ≤ N := (le_max_right m n).trans (le_max_right _ _)
  have hfirst := hm N hmN
  have hsecond := hn N hnN
  have htri := D.Cog_triangle x (s N) y
  rw [D.Cog_congr (s N) y (t N) (hst N hk), D.Cog_symm (t N) y] at htri
  linarith
