-- Prove2me | solution 1 for Formalism.F.muMaxLeMin_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:09.112554+00:00
-- url     : https://prove2.me/submissions/90a11a1b-6863-4739-a785-e04ea7e59c77

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxLeMin
import Theorems.Thm_Formalism_F_att_rk_le
import Theorems.Thm_Formalism_F_att_rk_pos
import Theorems.Thm_Formalism_F_discreteTopology_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.F
universe u
namespace Formalism.F
theorem _root_.solution (hP : CovolPos.{u}) (hS : ShortVector.{u}) : MuMaxLeMin.{u} := by
  intro E _ _ _ L hL hL0 r hr hmin
  haveI := hL
  have hne : (slopes L).Nonempty := ⟨slope L, L, le_rfl, hL0, rfl⟩
  unfold muMax
  apply csSup_le hne
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI : DiscreteTopology N := discreteTopology_of_le hNL
  have hk : 0 < rk N := att_rk_pos hN0
  have hkL : rk N ≤ rk L := att_rk_le hNL
  have hc : 0 < covol N := hP E N inferInstance
  obtain ⟨v, hvN, hv0, hvle⟩ := hS E N inferInstance hN0
  have hrv : r ≤ ‖v‖ := hmin v (hNL hvN) hv0
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk

  have h1 : Real.log r ≤ Real.log (rk N : ℝ) / 2 + Real.log (covol N) / (rk N : ℝ) := by
    have hpow : 0 < covol N ^ ((1 : ℝ) / (rk N : ℝ)) := Real.rpow_pos_of_pos hc _
    have hsq : 0 < Real.sqrt (rk N : ℝ) := Real.sqrt_pos.mpr hk'
    have h := Real.log_le_log hr (hrv.trans hvle)
    rw [Real.log_mul hsq.ne' hpow.ne', Real.log_sqrt hk'.le, Real.log_rpow hc] at h
    have e : (1 : ℝ) / (rk N : ℝ) * Real.log (covol N) = Real.log (covol N) / (rk N : ℝ) := by ring
    linarith
  have h2 : Real.log (rk N : ℝ) ≤ Real.log (rk L : ℝ) :=
    Real.log_le_log hk' (by exact_mod_cast hkL)
  have h3 : slope N = -(Real.log (covol N) / (rk N : ℝ)) := by
    unfold slope deg; ring
  rw [h3]
  linarith
end Formalism.F
