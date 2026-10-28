-- Prove2me | solution 1 for BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T05:43:23.726983+00:00
-- url     : https://prove2.me/submissions/12421b2f-bd4c-4c7d-9496-db7ed8eaa0a9

-- Generated from ChapterFarisLavineOnly.lean — solution of BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx
import Mathlib
import Definitions.Def_ChapterFarisLavineOnly
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_norm_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData



open scoped ENNReal

noncomputable section


open BookProof.FarisLavine


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (d : CoreData F)

set_option maxHeartbeats 1000000 in
theorem solution (x : d.C.dom) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : d.C.dom, (y : F) ∈ d.C₀ ∧ ‖(y : F) - (x : F)‖ < ε ∧ ‖d.ext y - d.ext x‖ < ε := by

  have hK := d.hK
  have hpos : 0 < 2 * d.K + 2 := by linarith
  set δ : ℝ := min ε (ε / (2 * d.K + 2)) with hδdef
  have hδ : 0 < δ := lt_min hε (by positivity)
  obtain ⟨y, hyC, h1, h2⟩ := d.gc.approx x δ hδ
  refine ⟨y, hyC, lt_of_lt_of_le h1 (min_le_left _ _), ?_⟩
  have hsub : d.ext y - d.ext x = d.ext (y - x) := (map_sub _ _ _).symm
  have hcoe : ((y - x : d.C.dom) : F) = (y : F) - (x : F) := rfl
  have hop : d.C.op (y - x) = d.C.op y - d.C.op x := map_sub _ _ _
  have hb := d.ext_norm_le (y - x)
  rw [hop, hcoe] at hb
  have htri : ‖d.C.op y - d.C.op x + ((y : F) - (x : F))‖ ≤ δ + δ :=
    le_trans (norm_add_le _ _) (add_le_add h2.le h1.le)
  have hstep : ‖d.ext (y - x)‖ ≤ d.K * (δ + δ) :=
    le_trans hb (mul_le_mul_of_nonneg_left htri hK)
  have hδle : δ ≤ ε / (2 * d.K + 2) := min_le_right _ _
  have hfin : d.K * (δ + δ) < ε := by
    have h2δ : 2 * d.K * δ ≤ 2 * d.K * (ε / (2 * d.K + 2)) := by
      have : 0 ≤ 2 * d.K := by linarith
      exact mul_le_mul_of_nonneg_left hδle this
    have hlt : 2 * d.K * (ε / (2 * d.K + 2)) < ε := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ hpos]
      nlinarith
    have : d.K * (δ + δ) = 2 * d.K * δ := by ring
    linarith
  rw [hsub]
  exact lt_of_le_of_lt hstep hfin
