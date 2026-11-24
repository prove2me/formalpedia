-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.conj_geo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:22.374644+00:00
-- url     : https://prove2.me/submissions/d4aa10dc-60e9-44fc-9d64-686e51b102ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfConj
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_conj_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {G G' Z : Matrix ι ι K} (h : G * G' = 1) (N : ℕ) : G' * geo N Z * G = geo N (G' * Z * G) := by
  unfold geo
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => conj_pow h j
end Formalism.L2.SG.Pf.Unip
