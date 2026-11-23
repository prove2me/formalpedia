-- Prove2me | solution 1 for Formalism.HN.duality_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:10.211486+00:00
-- url     : https://prove2.me/submissions/7430c873-63b1-4cd7-93be-6eb7c0954b72

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_inner_sum_dual
import Theorems.Thm_Formalism_HN_duality_eq_zero_of_inner

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
theorem _root_.solution (v w : ι → E) (hw : ∀ i, w i ∈ span ℝ (Set.range v))
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) {y : E}
    (hy : y ∈ span ℝ (Set.range v)) : y = ∑ k, inner ℝ (v k) y • w k := by
  have hs : (∑ k, inner ℝ (v k) y • w k) ∈ span ℝ (Set.range v) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hw k)
  have h0 := duality_eq_zero_of_inner v (Submodule.sub_mem _ hy hs) fun j => by
    have h2 := duality_inner_sum_dual v w hvw (fun k => inner ℝ (v k) y) j
    rw [inner_sub_right, sub_eq_zero]
    exact h2.symm
  exact sub_eq_zero.mp h0
end Formalism.HN
