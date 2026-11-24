-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.vars_of_polB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:24:20.515495+00:00
-- url     : https://prove2.me/submissions/23e4ac1b-9c96-4cc0-8fcc-8bf210603a6c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_sum


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
theorem _root_.solution {R : Type*} [CommRing R] {n N : ℕ} {B : ℕ → ℕ} {G : MvPolynomial (ℕ × Fin n) R}
    (hG : G ∈ polB R n N B) : ∀ x ∈ G.vars, x.1 < N := by
  intro x hx
  by_contra hlt
  push_neg at hlt
  have hGi := (Submodule.mem_iInf _).mp hG x.1
  rw [if_neg (not_lt.mpr hlt), mem_weightedHomogeneousSubmodule] at hGi
  obtain ⟨e, he, hex⟩ := (MvPolynomial.mem_vars x).mp hx
  have h0 := hGi (mem_support_iff.mp he)
  have hpos : 0 < e x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hex)
  rw [Finsupp.weight_apply, Finsupp.sum] at h0
  have hle := Finset.single_le_sum (f := fun y => e y • (if y.1 = x.1 then 1 else 0 : ℕ))
    (fun _ _ => Nat.zero_le _) hex
  simp only [if_true, smul_eq_mul, mul_ite, mul_one, mul_zero] at hle h0
  omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
