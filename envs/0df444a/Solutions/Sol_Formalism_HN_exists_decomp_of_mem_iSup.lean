-- Prove2me | solution 1 for Formalism.HN.exists_decomp_of_mem_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:19.048488+00:00
-- url     : https://prove2.me/submissions/04b0f16b-d74c-4caa-a2bc-6834c8e20fd6

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {P E : Type*} [Fintype P] [AddCommGroup E] [Module ℝ E]
    (p : P → Submodule ℝ E) {x : E} (hx : x ∈ ⨆ v, p v) :
    ∃ f : P → E, (∀ v, f v ∈ p v) ∧ ∑ v, f v = x := by
  classical
  induction hx using Submodule.iSup_induction' with
  | mem i y hy =>
    refine ⟨Pi.single i y, fun v => ?_, by simp⟩
    by_cases h : v = i
    · subst h
      simpa using hy
    · simp [h]
  | zero => exact ⟨0, fun v => zero_mem _, by simp⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨f, hf, rfl⟩ := ihy
    obtain ⟨g, hg, rfl⟩ := ihz
    exact ⟨f + g, fun v => add_mem (hf v) (hg v), by simp [Finset.sum_add_distrib]⟩
end Formalism.HN
