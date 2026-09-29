-- Prove2me | solution 1 for Freiman.trunk_normal_use_valid
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:27:08.144474+00:00
-- url     : https://prove2.me/submissions/67a5379f-935b-4ef9-98ec-8c38034d0b41

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hz : w.diagonal = 0)
    (l u : CertBound) (hu : trunkUseBounds C w l u) :
    certWitnessValid ⟨l,u,w.rectangle,certBernsteinCoefficients (trunkPolynomial C w) w.rectangle,fun _ _ => w.margin/2⟩ := by
  have hv := hw.2.2.2.2
  rw [if_pos hz] at hv
  rcases hu with ⟨hl, hu, hlt, hut, hs⟩
  dsimp [certWitnessValid, trunkPairWitness] at hv
  rcases hv with ⟨_, _, hr, hr0, hltv, hutv, _, hbounds, _⟩
  dsimp [certWitnessValid]
  refine ⟨hl, hu, hr, hr0, ?_, ?_, ?_, hbounds, ?_⟩
  · simpa only [hlt] using hltv
  · simpa only [hut] using hutv
  · simp only [hlt, hut, trunkPolynomial]
  · rcases hs with ⟨_, hm⟩ | hl | hu
    · left
      intro i j
      exact div_pos hm (by norm_num)
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr hu)
