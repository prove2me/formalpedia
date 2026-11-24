-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.sharp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:35.536173+00:00
-- url     : https://prove2.me/submissions/2cb459f2-3fef-4213-9318-af53b734f26f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool

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
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
variable {J J' : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (c : K) (M : Matrix ι ι K) : sharp J J' (c • M) = star c • sharp J J' M := by
  simp only [sharp, conjTranspose_smul, mul_smul_comm, smul_mul_assoc]
end Formalism.L2.SG.Pf.Unip
