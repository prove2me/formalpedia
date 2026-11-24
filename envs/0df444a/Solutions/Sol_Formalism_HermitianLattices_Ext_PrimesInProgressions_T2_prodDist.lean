-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodDist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.896096+00:00
-- url     : https://prove2.me/submissions/5c772f2c-8115-4690-a0ae-a4abe436c45a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsFarFromPoints
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_exists_far_from_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) (c r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| :=
  exists_far_from_points t s.card s rfl c r hr
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
