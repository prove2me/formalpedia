-- Prove2me | solution 1 for BertsekasShreve.BorelFinite.cor8_1_1_markov_inf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:57:22.004084+00:00
-- url     : https://prove2.me/submissions/984a2382-a546-409f-b55f-2619e91ce031
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Theorems.Thm_BertsekasShreve_BorelFinite_prop8_1_markov_equivalent

open BertsekasShreve.BorelFinite

theorem solution {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M ∨ FMinus M) (K : ℕ) (hK1 : 1 ≤ K) (hKN : K ≤ M.N) :
    ∀ x : S, Jstar M K x = ⨅ (π : Policy M) (_ : π.IsMarkov), J M K π x := by
  intro x
  apply le_antisymm
  · -- the Markov policies form a subset of `Π′`
    exact le_iInf₂ fun π _ => iInf_le (fun π : Policy M => J M K π x) π
  · -- every policy is matched at `x` by a Markov policy (Proposition 8.1)
    refine le_iInf fun π' => ?_
    obtain ⟨π, hπ, hJ⟩ := prop8_1_markov_equivalent M hF x π'
    rw [← hJ K hK1 hKN]
    exact iInf₂_le π hπ
