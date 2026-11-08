-- Prove2me | solution 1 for ChenMaxEnt.discontinuous_of_seq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:56:40.367634+00:00
-- url     : https://prove2.me/submissions/a48663b0-0c32-4a13-af4c-e301007d9e4b

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ChenMaxEnt_expectations
import Definitions.Def_ChenMaxEnt_jointRange
import Definitions.Def_ChenMaxEnt_linearFamily
import Definitions.Def_ChenMaxEnt_maxEntInference
import Definitions.Def_ChenMaxEnt_groundEnergy
import Definitions.Def_ChenMaxEnt_groundSpace
import Definitions.Def_ChenMaxEnt_maximallyMixedOn

open QAlgorithms Filter Topology

open ChenMaxEnt in
theorem solution {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (F : ι → Matrix n n ℂ) (hF : ∀ i, (F i).IsHermitian) (α : ι → ℝ) (αs : ℕ → ι → ℝ)
    (hαs : ∀ s, αs s ∈ jointRange F) (hlim : Tendsto αs atTop (𝓝 α))
    (hnot : ¬ Tendsto (fun s => maxEntInference F (αs s)) atTop (𝓝 (maxEntInference F α))) :
    ¬ ContinuousWithinAt (maxEntInference F) (jointRange F) α := by
  intro hc
  apply hnot
  have h1 : Tendsto αs atTop (𝓝[jointRange F] α) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hαs⟩
  exact hc.tendsto.comp h1
