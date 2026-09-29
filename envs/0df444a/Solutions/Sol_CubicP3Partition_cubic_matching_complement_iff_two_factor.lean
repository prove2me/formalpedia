-- Prove2me | solution 1 for CubicP3Partition.cubic_matching_complement_iff_two_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T04:57:50.254582+00:00
-- url     : https://prove2.me/submissions/13c3edf3-0196-48c5-9898-68d7415026b6

import Mathlib
import Definitions.Def_cubic_p3_partition_models

open CubicP3Partition

universe u

theorem solution {V : Type u} [Fintype V] (G : SimpleGraph V) (hCubic : Cubic G) :
    HasDivisibleComplement G ↔ HasDivisibleTwoFactor G := by
  classical
  have hcard : ∀ (P : V → Prop) [DecidablePred P],
      Nat.card {w // P w} = (Finset.univ.filter (fun w => P w)).card := by
    intro P _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  constructor
  · rintro ⟨M, -, hF⟩
    exact ⟨_, hF⟩
  · rintro ⟨F, ⟨hFle, hFdeg⟩, hdiv⟩
    refine ⟨G ⊓ Fᶜ, ⟨inf_le_left, ?_⟩, ?_⟩
    · -- the complement of a 2-factor inside a cubic graph is a perfect matching
      intro v
      have hsub : (Finset.univ.filter (fun w => F.Adj v w))
          ⊆ (Finset.univ.filter (fun w => G.Adj v w)) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact hFle hw
      have hset : (Finset.univ.filter (fun w => (G ⊓ Fᶜ).Adj v w))
          = (Finset.univ.filter (fun w => G.Adj v w))
            \ (Finset.univ.filter (fun w => F.Adj v w)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          SimpleGraph.inf_adj, SimpleGraph.compl_adj]
        constructor
        · rintro ⟨h1, -, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, G.ne_of_adj h1, h2⟩
      have hG : (Finset.univ.filter (fun w => G.Adj v w)).card = 3 := by
        have := hCubic v
        rwa [degree, hcard] at this
      have hF : (Finset.univ.filter (fun w => F.Adj v w)).card = 2 := by
        have := hFdeg v
        rwa [degree, hcard] at this
      rw [degree, hcard, hset, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hG, hF]
    · -- the matching complement is exactly `F` again
      have hMC : matchingComplement G (G ⊓ Fᶜ) = F := by
        rw [matchingComplement, compl_inf, compl_compl, inf_sup_left, inf_compl_self,
          bot_sup_eq, inf_eq_right.mpr hFle]
      rw [hMC]
      exact ⟨⟨hFle, hFdeg⟩, hdiv⟩
