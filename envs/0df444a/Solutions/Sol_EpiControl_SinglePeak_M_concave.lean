-- Prove2me | solution 1 for EpiControl.SinglePeak.M_concave
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:50:41.004998+00:00
-- url     : https://prove2.me/submissions/4e8bf07d-f3af-47d7-b4ef-6a604020106a

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace Aux_EpiControl_M_concave
open EpiControl.SinglePeak

theorem bdd (P : Params) (hP : P.Standing) (y : ℝ) :
    BddBelow ((fun b => y * b + P.c b) '' Icc P.bl P.bbar) :=
  isCompact_Icc.bddBelow_image
    ((continuousOn_const.mul continuousOn_id).add hP.c_cont)

theorem nonempty (P : Params) (hP : P.Standing) (y : ℝ) :
    ((fun b => y * b + P.c b) '' Icc P.bl P.bbar).Nonempty :=
  ⟨_, P.bl, ⟨le_rfl, hP.bl_lt_bbar.le⟩, rfl⟩

end Aux_EpiControl_M_concave

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) :
    ConcaveOn ℝ univ P.M := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold Params.M
  apply le_csInf (Aux_EpiControl_M_concave.nonempty P hP _)
  rintro _ ⟨z, hz, rfl⟩
  have hx := csInf_le (Aux_EpiControl_M_concave.bdd P hP x) ⟨z, hz, rfl⟩
  have hy := csInf_le (Aux_EpiControl_M_concave.bdd P hP y) ⟨z, hz, rfl⟩
  simp only at hx hy ⊢
  have e : (a * x + b * y) * z + P.c z = a * (x * z + P.c z) + b * (y * z + P.c z) := by
    have : P.c z = (a + b) * P.c z := by rw [hab, one_mul]
    linear_combination this
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
