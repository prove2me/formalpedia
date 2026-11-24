-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.vars_actX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:21.437671+00:00
-- url     : https://prove2.me/submissions/4a95adaf-0620-4b29-a3b1-e8c3f0993436

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_DominanceOrderLemmas_actAll_X

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
theorem _root_.solution {L : Type*} [CommRing L] [Nontrivial L] {n : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (x : ℕ × Fin n) :
    ∀ y ∈ (actAll isVec g gi (X x)).vars, y.1 = x.1 := by
  intro y hy
  rw [actAll_X] at hy
  split_ifs at hy <;>
  · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hy)
    have h' := MvPolynomial.vars_mul _ _ hb
    rw [Finset.mem_union, vars_X, vars_C] at h'
    simp only [Finset.mem_singleton, Finset.notMem_empty, or_false] at h'
    rw [h']
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
