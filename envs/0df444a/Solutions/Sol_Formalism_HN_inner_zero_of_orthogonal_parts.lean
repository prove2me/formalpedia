-- Prove2me | solution 1 for Formalism.HN.inner_zero_of_orthogonal_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:29.449129+00:00
-- url     : https://prove2.me/submissions/04162b36-b770-411f-a871-79a5827dd628

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_exists_decomp_of_mem_iSup

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
theorem _root_.solution {P E : Type*} [Fintype P] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (Ev : P → Submodule ℝ E) (hEv : ∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0)
    (T : Submodule ℝ E) (hT : T = ⨆ v, T ⊓ Ev v) {v : P} {x : E} (hxv : x ∈ Ev v)
    (hx : ∀ t ∈ T ⊓ Ev v, inner ℝ t x = 0) : ∀ t ∈ T, inner ℝ t x = 0 := by
  intro t ht
  rw [hT] at ht
  obtain ⟨f, hf, rfl⟩ := exists_decomp_of_mem_iSup (fun w => T ⊓ Ev w) ht
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : w = v
  · subst hw
    exact hx _ (hf w)
  · exact hEv w v hw _ (hf w).2 x hxv
end Formalism.HN
