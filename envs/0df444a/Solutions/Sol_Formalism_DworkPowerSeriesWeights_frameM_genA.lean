-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frameM_genA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:52.132896+00:00
-- url     : https://prove2.me/submissions/d9ed642d-f61d-4d36-b4d1-cf319cb230a0

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_ZV_slice

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
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d] (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (x xg : ZMod d × Fin N0 × Fin N0 → K)
    (hxg : ∀ s i a, xg (s, i, a) = ∑ k : Fin N0, effMat TT T s i k * x (s, k, a))
    (z i : ZV d N0 N1) :
    frameM (N1 := N1) xg z i = ∑ y, frameM (N1 := N1) x z y * genA TT T i y := by
  classical
  rw [sum_ZV_slice z.1 z.2.2]
  · simp only [frameM, genA, eq_self_iff_true, and_self, ↓reduceIte]
    by_cases h : i.1 = z.1 ∧ i.2.2 = z.2.2
    · rw [if_pos h, hxg]
      obtain ⟨h1, h2⟩ := h
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [if_pos ⟨h1.symm, h2.symm⟩, h1]
      ring
    · rw [if_neg h]
      refine (Finset.sum_eq_zero (fun k _ => ?_)).symm
      rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), mul_zero]
  · intro y hy
    simp only [frameM]
    rw [if_neg hy, zero_mul]
end Formalism.DworkPowerSeriesWeights
