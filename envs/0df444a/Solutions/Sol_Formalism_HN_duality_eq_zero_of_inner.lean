-- Prove2me | solution 1 for Formalism.HN.duality_eq_zero_of_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:18.513918+00:00
-- url     : https://prove2.me/submissions/101d6b23-dfec-4120-806f-a52fa60a5718

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HN
theorem _root_.solution (v : ι → E) {z : E} (hz : z ∈ span ℝ (Set.range v))
    (h : ∀ k, inner ℝ (v k) z = 0) : z = 0 := by
  have hall : ∀ u ∈ span ℝ (Set.range v), inner ℝ u z = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact h k
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  have hzz := hall z hz
  exact inner_self_eq_zero.mp hzz
end Formalism.HN
