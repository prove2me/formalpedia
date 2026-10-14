-- Prove2me | solution 1 for Freiman.gap_extremizer_B_data
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T19:56:44.333062+00:00
-- url     : https://prove2.me/submissions/b7d74684-b266-402f-ac5c-b935840d22eb

import Definitions.Def_Freiman_gapModel

namespace GapExtremizerBDataAux

open Freiman

/-- `L[j]!` is either a genuine member of `L` or the default `1`, so a uniform
bound on the members bounds it for every index. -/
private lemma getBang_le (L : List ℕ+) (hL : ∀ x ∈ L, (x : ℕ) ≤ 4) (j : ℕ) :
    ((L[j]! : ℕ+) : ℕ) ≤ 4 := by
  by_cases hj : j < L.length
  · rw [getElem!_pos L j hj]
    exact hL _ (List.getElem_mem hj)
  · rw [getElem!_neg L j hj]
    decide

private lemma gapEP_le (u v : List ℕ+)
    (hu : ∀ x ∈ u, (x : ℕ) ≤ 4) (hv : ∀ x ∈ v, (x : ℕ) ≤ 4) (n : ℕ) :
    ((gapEventuallyPeriodic u v n : ℕ+) : ℕ) ≤ 4 := by
  unfold gapEventuallyPeriodic
  split_ifs
  · exact getBang_le u hu n
  · exact getBang_le v hv _

private lemma gapBLeft_le (n : ℕ) : ((gapBLeft n : ℕ+) : ℕ) ≤ 4 :=
  gapEP_le _ _ (by decide) (by decide) n

private lemma gapBRight_le (n : ℕ) : ((gapBRight n : ℕ+) : ℕ) ≤ 4 :=
  gapEP_le _ _ (by decide) (by decide) n

lemma digits : gapDigits gapExtremizerB := by
  intro i
  unfold gapExtremizerB gapJoin
  split_ifs
  · decide
  · exact gapBLeft_le _
  · exact gapBRight_le _

lemma seed : gapMatch gapExtremizerB 0 gapSeedB := by
  refine ⟨by decide, ?_⟩
  decide

end GapExtremizerBDataAux

theorem solution :
    Freiman.gapDigits Freiman.gapExtremizerB ∧
      Freiman.gapMatch Freiman.gapExtremizerB 0 Freiman.gapSeedB :=
  ⟨GapExtremizerBDataAux.digits, GapExtremizerBDataAux.seed⟩
