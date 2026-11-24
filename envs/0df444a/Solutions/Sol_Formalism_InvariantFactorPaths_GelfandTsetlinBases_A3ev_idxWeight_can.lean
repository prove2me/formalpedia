-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.idxWeight_can
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:52.202884+00:00
-- url     : https://prove2.me/submissions/6146ee35-2e7a-4cad-a299-6e65c273e288

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_mem_can


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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
theorem _root_.solution {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) : idxWeight (canIdx μ) = μ := by
  funext m
  unfold idxWeight
  have h1 : {c : ℤ | 1 ≤ c ∧ m ∈ canIdx μ c} = ↑(Finset.Icc 1 (μ m)) := by
    ext c
    rw [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨a, b⟩
      rw [A1hw.mem_can h, if_pos a] at b
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      refine ⟨a, ?_⟩
      rw [A1hw.mem_can h, if_pos a]
      exact b
  have h2 : {c : ℤ | c ≤ 0 ∧ m ∈ canIdx μ c} = ↑(Finset.Ioc (μ m) 0) := by
    ext c
    rw [Finset.mem_coe, Finset.mem_Ioc]
    constructor
    · rintro ⟨a, b⟩
      rw [A1hw.mem_can h, if_neg (by omega)] at b
      exact ⟨b, a⟩
    · rintro ⟨a, b⟩
      refine ⟨b, ?_⟩
      rw [A1hw.mem_can h, if_neg (by omega)]
      exact a
  rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, Int.card_Icc, Int.card_Ioc]
  omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
