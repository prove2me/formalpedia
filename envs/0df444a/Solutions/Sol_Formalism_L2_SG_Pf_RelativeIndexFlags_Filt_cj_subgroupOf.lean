-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.cj_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:58:06.300669+00:00
-- url     : https://prove2.me/submissions/1cef6810-72ea-4af0-8cbc-375d2a67e5f5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_FiltRelIndex
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexUnipotentConjSymm
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_mem_cj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ∈ L) (hX : X ≤ L) :
    (cj g X).subgroupOf L = cj ⟨g, hg⟩ (X.subgroupOf L) := by
  ext y
  rw [Subgroup.mem_subgroupOf, mem_cj, mem_cj]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨⟨x, hX hx⟩, by rw [Subgroup.mem_subgroupOf]; exact hx, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hxy
  · rintro ⟨x, hx, hxy⟩
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨x, hx, ?_⟩
    rw [← hxy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
