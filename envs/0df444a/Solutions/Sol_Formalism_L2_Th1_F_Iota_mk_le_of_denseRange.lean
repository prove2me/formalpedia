-- Prove2me | solution 1 for Formalism.L2.Th1.F.Iota.mk_le_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:18:20.733295+00:00
-- url     : https://prove2.me/submissions/b2d78246-3414-40b5-a116-d8344bb2363c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Cardinal Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Iota
namespace Formalism.L2.Th1.F.Iota
theorem _root_.solution {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  have h : ∀ x : X, ∃ u : ℕ → D, Tendsto (fun n => f (u n)) atTop (𝓝 x) := by
    intro x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose u hu using hv
    exact ⟨u, by simpa only [hu] using hlim⟩
  choose g hg using h
  have hinj : Function.Injective g := by
    intro x y hxy
    have := hg y
    rw [← hxy] at this
    exact tendsto_nhds_unique (hg x) this
  have := mk_le_of_injective hinj
  simpa using this
end Formalism.L2.Th1.F.Iota
