-- Prove2me | solution 1 for EpiControl.SinglePeak.M_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:49:23.718292+00:00
-- url     : https://prove2.me/submissions/731d66e5-cc13-4b3a-bb7d-a0f02b9fc684

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace Aux_EpiControl_M_monotone
open EpiControl.SinglePeak

theorem bdd (P : Params) (hP : P.Standing) (y : ℝ) :
    BddBelow ((fun b => y * b + P.c b) '' Icc P.bl P.bbar) :=
  isCompact_Icc.bddBelow_image
    ((continuousOn_const.mul continuousOn_id).add hP.c_cont)

theorem nonempty (P : Params) (hP : P.Standing) (y : ℝ) :
    ((fun b => y * b + P.c b) '' Icc P.bl P.bbar).Nonempty :=
  ⟨_, P.bl, ⟨le_rfl, hP.bl_lt_bbar.le⟩, rfl⟩

end Aux_EpiControl_M_monotone

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) :
    Monotone P.M := by
  intro y y' hyy
  unfold Params.M
  apply le_csInf (Aux_EpiControl_M_monotone.nonempty P hP y')
  rintro _ ⟨b, hb, rfl⟩
  have hb0 : 0 ≤ b := le_trans hP.bl_pos.le hb.1
  calc sInf ((fun b => y * b + P.c b) '' Icc P.bl P.bbar) ≤ y * b + P.c b :=
        csInf_le (Aux_EpiControl_M_monotone.bdd P hP y) ⟨b, hb, rfl⟩
    _ ≤ y' * b + P.c b := by nlinarith
