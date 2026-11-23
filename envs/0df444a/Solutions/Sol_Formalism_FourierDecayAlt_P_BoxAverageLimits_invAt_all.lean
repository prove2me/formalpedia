-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.invAt_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:52.422588+00:00
-- url     : https://prove2.me/submissions/bb9ffc62-f35a-4994-99f4-1e5f24445c8b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_LIMf_shift_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_invAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_invAt_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_invAt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (he : AddSubgroup.closure (Set.range e) = ⊤) (σ : Λ) :
    InvAt e c σ := by
  have hσ : σ ∈ AddSubgroup.closure (Set.range e) := by rw [he]; exact AddSubgroup.mem_top σ
  induction hσ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    intro g hg; exact LIMf_shift_gen e c g hg j
  | zero => exact invAt_zero e c
  | add x y _ _ hx hy => exact invAt_add e c x y hx hy
  | neg x _ hx => exact invAt_neg e c x hx
end Formalism.FourierDecayAlt.P.BoxAverageLimits
