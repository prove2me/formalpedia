-- Prove2me | solution 1 for Freiman.gap_extremizer_A_data
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T19:43:01.424369+00:00
-- url     : https://prove2.me/submissions/a07c1abf-369b-4466-ab2b-9bec72b95d24

import Definitions.Def_Freiman_gapModel

namespace GapExtremizerADataAux

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

private lemma gapALeft_le (n : ℕ) : ((gapALeft n : ℕ+) : ℕ) ≤ 4 :=
  gapEP_le _ _ (by decide) (by decide) n

private lemma gapARight_le (n : ℕ) : ((gapARight n : ℕ+) : ℕ) ≤ 4 :=
  gapEP_le _ _ (by decide) (by decide) n

lemma digits : gapDigits gapExtremizerA := by
  intro i
  unfold gapExtremizerA gapJoin
  split_ifs
  · decide
  · exact gapALeft_le _
  · exact gapARight_le _

lemma seed : gapMatch gapExtremizerA 0 gapSeedA := by
  refine ⟨by decide, ?_⟩
  decide

end GapExtremizerADataAux

theorem solution :
    Freiman.gapDigits Freiman.gapExtremizerA ∧
      Freiman.gapMatch Freiman.gapExtremizerA 0 Freiman.gapSeedA :=
  ⟨GapExtremizerADataAux.digits, GapExtremizerADataAux.seed⟩
