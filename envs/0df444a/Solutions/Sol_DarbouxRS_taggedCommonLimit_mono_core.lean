-- Prove2me | solution 1 for DarbouxRS.taggedCommonLimit_mono_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:12:16.06096+00:00
-- url     : https://prove2.me/submissions/30d79883-01ae-4bbc-ad21-e2a7657ef1c7

import Theorems.Thm_exists_partition_mesh_lt
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_taggedSum_mono_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    Lf ≤ Lg := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨_hsg, hlimg⟩

  -- Create a copy of `hsf` so we can extract `hab` without destroying `hsf`
  have hsf_copy := hsf
  rcases hsf_copy with ⟨hab, _hAbove, _hBelow, _hmono⟩

  rw [le_iff_forall_pos_lt_add]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  rcases exists_partition_mesh_lt hab (lt_min hδf hδg) with ⟨P, hPmesh⟩

  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- We already proved this earlier!
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmeshf : P.mesh < δf := lt_of_lt_of_le hPmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hPmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg

  -- Pass `hsf` cleanly without rebuilding it!
  have hsum : taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
    taggedSum_mono_core P tags hsf htags hfg

  have hf_bound : Lf < taggedSum P tags f alpha + eps / 2 := by
    have hleft := (abs_lt.mp hPf).1
    linarith
  have hg_bound : taggedSum P tags g alpha < Lg + eps / 2 := by
    have hright := (abs_lt.mp hPg).2
    linarith
  linarith
