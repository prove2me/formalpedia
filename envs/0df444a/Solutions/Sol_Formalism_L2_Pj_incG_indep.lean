-- Prove2me | solution 1 for Formalism.L2.Pj.incG_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:03.886186+00:00
-- url     : https://prove2.me/submissions/d17d6b45-6eab-4240-9f92-3f5019c5c285

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
import Theorems.Thm_Formalism_L2_Pj_coeff_incG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
namespace Formalism.L2.Pj
theorem _root_.solution (hkey : Function.Injective key) :
    iSupIndep fun w : W => LinearMap.range (incG key C w) := by
  intro w
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨F, rfl⟩ := LinearMap.mem_range.mp hx
  have hle : (⨆ (u) (_ : u ≠ w), LinearMap.range (incG key C u)) ≤ LinearMap.ker (cfG K (key w)) := by
    refine iSup₂_le fun u hu => ?_
    rintro _ ⟨G', rfl⟩
    rw [LinearMap.mem_ker]
    change (incG key C u G').coeff (key w) = 0
    rw [coeff_incG, if_neg (fun h => hu (hkey h))]
  have h0 : (incG key C w F).coeff (key w) = 0 := hle hx'
  rw [coeff_incG, if_pos rfl] at h0
  rw [show F = 0 from Subtype.ext h0, map_zero]
end Formalism.L2.Pj
