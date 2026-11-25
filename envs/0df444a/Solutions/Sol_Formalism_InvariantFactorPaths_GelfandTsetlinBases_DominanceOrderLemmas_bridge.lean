-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.bridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:37.74661+00:00
-- url     : https://prove2.me/submissions/ad94366d-17e7-4df0-a2fa-9867c5547e0e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_DominanceOrderLemmas_actAll_X
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_act_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_genPoint_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace DominanceOrderLemmas
private lemma rename_actAll_eq_sharpHom {L : Type*} [CommRing L] {n N : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (P : MvPolynomial (ℕ × Fin n) L) (hv : ∀ x ∈ P.vars, x.1 < N) :
    rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty) (actAll isVec g gi P) =
      sharpHom (ζ := Empty) isVec {j : ℕ | j < N} g gi (rename Sum.inl P) := by
  have h := MvPolynomial.hom_congr_vars
    (f₁ := ((rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty)).comp (actAll isVec g gi)).toRingHom)
    (f₂ := ((sharpHom (ζ := Empty) isVec {j : ℕ | j < N} g gi).comp
      (rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty))).toRingHom) (p₁ := P) (p₂ := P) ?_ ?_ rfl
  · simpa using h
  · exact RingHom.ext fun a => by simp
  · rintro ⟨i, a⟩ hi _
    have hiN : i < N := hv _ hi
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, rename_X, actAll_X]
    simp only [sharpHom, aeval_X, Set.mem_setOf_eq, hiN, if_true]
    split_ifs <;> simp [Matrix.vecMul, dotProduct]
end DominanceOrderLemmas
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
theorem _root_.solution (k : Type) [Field k] {n N : ℕ} (isVec : ℕ → Bool) {G : MvPolynomial (ℕ × Fin n) k}
    (hv : ∀ x ∈ G.vars, x.1 < N) :
    rename Sum.inl (actAll isVec (genMat k n) (genMat k n)⁻¹ (map (algebraMap k (GenField k n)) G)) =
      genPoint (ζ := Empty) isVec {j : ℕ | j < N} (rename Sum.inl G) := by
  rw [GS.genPoint_eq]
  have ha := GS.act_eq (ζ := Empty) (isVec := isVec) (S := {j : ℕ | j < N}) (genMat k n)
    GS.genMat_isUnit (rename Sum.inl G)
  refine Eq.trans ?_ ha
  rw [map_rename]
  exact rename_actAll_eq_sharpHom isVec _ _ _ (fun x hx => hv x (vars_map _ _ hx))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
