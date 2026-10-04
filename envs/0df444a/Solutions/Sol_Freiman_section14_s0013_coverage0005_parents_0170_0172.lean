-- Prove2me | solution 1 for Freiman.section14_s0013_coverage0005_parents_0170_0172
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T12:16:45.827576+00:00
-- url     : https://prove2.me/submissions/7b220a3e-ed82-44f3-ba9f-2564325e2a50

import Theorems.Thm_Freiman_section14_s0013_coverage0005_parents_0170_0171

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false

open Freiman

namespace Parent171Certificate

private theorem recordPart6 {r : Section14Record}
    (h : r ∈ section14DataRecords2Part3) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records =
      (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++
        section14DataRecords1Part3 ++ section14DataRecords1Part4 ++
        section14DataRecords2Part1 ++ section14DataRecords2Part2) ++
      section14DataRecords2Part3 ++
      (section14DataRecords2Part4 ++ section14DataRecords3Part1 ++
        section14DataRecords3Part2 ++ section14DataRecords3Part3 ++
        section14DataRecords3Part4 ++ section14DataRecords4Part1 ++
        section14DataRecords4Part2 ++ section14DataRecords4Part3 ++
        section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2,
      section14DataRecords3, section14DataRecords4, List.append_assoc,
      List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))

private theorem recorded (r : Section14Record)
    (hr : r ∈ section14Catalog.records) (si parent : ℕ)
    (hs : si ∈ r.states) (hp : parent ∈ r.parents) :
    section14Recorded section14Catalog si parent r.goal r.branch :=
  ⟨r, hr, hs, hp, rfl, rfl⟩

theorem excludedGoal : section14Recorded section14Catalog 13 171 153 (-1) := by
  apply recorded
    (⟨153, (-1), [1, 2, 5, 6, 13, 14], [147, 151, 171, 175, 187, 191], 636⟩)
    ?_ 13 171 (by decide) (by decide)
  exact recordPart6
    (List.mem_of_getElem?
      (show section14DataRecords2Part3[850]? =
          some (⟨153, (-1), [1, 2, 5, 6, 13, 14],
            [147, 151, 171, 175, 187, 191], 636⟩) from rfl))

end Parent171Certificate

theorem solution : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 5).take 1,
    ∀ b ∈ ((section14Parents section14Catalog
      (section14State section14Catalog 13)).drop 170).take 2,
      section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨
      ∀ gs ∈ pl.specs,
        ∀ j ∈ List.range
          (section14GoalBranches section14Catalog
            (section14Goal section14Catalog gs.1)).length,
          (section14Branch section14Catalog
            (section14Goal section14Catalog gs.1) j).2 = .automatic ∨
          section14Recorded section14Catalog 13 b.branch gs.1 j := by
  intro pl hpl b hb
  have hbranch : b.branch = 170 ∨ b.branch = 171 := by
    have h : ∀ parent ∈ ((section14Parents section14Catalog
        (section14State section14Catalog 13)).drop 170).take 2,
        parent.branch = 170 ∨ parent.branch = 171 := by
      decide +kernel
    exact h b hb
  rcases hbranch with h170 | h171
  · have hb1 : b ∈ ((section14Parents section14Catalog
        (section14State section14Catalog 13)).drop 170).take 1 := by
      have h : ∀ parent ∈ ((section14Parents section14Catalog
          (section14State section14Catalog 13)).drop 170).take 2,
          parent.branch = 170 →
          parent ∈ ((section14Parents section14Catalog
            (section14State section14Catalog 13)).drop 170).take 1 := by
        decide +kernel
      exact h b hb h170
    exact Freiman.section14_s0013_coverage0005_parents_0170_0171 pl hpl b hb1
  · left
    have hexcluded : pl.excludedGoal = 153 := by
      have h : ∀ plan ∈ ((section14State section14Catalog 13).plans.drop 5).take 1,
          plan.excludedGoal = 153 := by
        decide +kernel
      exact h pl hpl
    rw [h171, hexcluded]
    exact Parent171Certificate.excludedGoal

#print axioms solution
