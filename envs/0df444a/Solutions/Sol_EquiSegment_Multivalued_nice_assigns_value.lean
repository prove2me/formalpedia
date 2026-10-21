-- Prove2me | solution 1 for EquiSegment.Multivalued.nice_assigns_value
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:41:27.836985+00:00
-- url     : https://prove2.me/submissions/db08742d-05c8-429e-b635-6d38c814dacb

import Mathlib
import Definitions.Def_EquiSegment_Multivalued_Setting

set_option autoImplicit false
open EquiSegment.Multivalued

theorem solution (Z : Set ((ℝ × ℝ) × ℝ)) (hZ : IsNice Z) :
    ∀ s ∈ Seg, ∃ y ∈ Set.Ioo (-1 : ℝ) 1, (s, y) ∈ Z := by
  obtain ⟨_, hsub, hsep⟩ := hZ
  intro s hs
  by_contra hcon
  push_neg at hcon
  have hSconn : IsPreconnected ((fun y : ℝ => (s, y)) '' Set.Icc (-1 : ℝ) 1) :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun y : ℝ => (s, y)).continuousOn
  have hSsub : (fun y : ℝ => (s, y)) '' Set.Icc (-1 : ℝ) 1 ⊆ Cyl \ Z := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨hs, hy⟩, fun hmem => ?_⟩
    exact hcon y (hsub hmem).2 hmem
  have hb : ((s, (-1 : ℝ))) ∈ Bottom := ⟨hs, rfl⟩
  have ht : ((s, (1 : ℝ))) ∈ EquiSegment.Multivalued.Top := ⟨hs, rfl⟩
  apply hsep.2.2 _ hb _ ht
  exact hSconn.subset_connectedComponentIn (x := (s, (-1 : ℝ)))
    ⟨-1, ⟨le_refl _, by norm_num⟩, rfl⟩ hSsub ⟨1, ⟨by norm_num, le_refl _⟩, rfl⟩
