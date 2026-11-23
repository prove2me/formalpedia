-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sum_ZV_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:31.999648+00:00
-- url     : https://prove2.me/submissions/38dcd749-e0fc-4725-a6eb-79e1d70d3ad4

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {d N0 N1 : ℕ} [NeZero d] {M : Type*} [AddCommMonoid M] (s : ZMod d)
    (b : Fin N1) (f : ZV d N0 N1 → M) (hf : ∀ y, ¬ (y.1 = s ∧ y.2.2 = b) → f y = 0) :
    ∑ y, f y = ∑ k, f (s, k, b) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image (fun k : Fin N0 => ((s, k, b) : ZV d N0 N1))))]
  · rw [Finset.sum_image]
    intro k₁ _ k₂ _ h
    simpa using h
  · intro y _ hy
    apply hf
    rintro ⟨h1, h2⟩
    exact hy (Finset.mem_image.mpr ⟨y.2.1, Finset.mem_univ _, Prod.ext h1.symm (Prod.ext rfl h2.symm)⟩)
end Formalism.DworkPowerSeriesWeights
