-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.fam_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:31.392705+00:00
-- url     : https://prove2.me/submissions/1b7b5542-5022-44fa-8393-858f677f7e81

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_pathProductLinearIndependent


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
theorem _root_.solution (hBrk : FactBrk) (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (μ₀ : Fin n → ℤ) (hanti : Antitone μ₀) :
    LinearIndepOn k (fam k (n := n) (N := N) (isVec := isVec) (B := B)) {x | x.1.1 N = μ₀} := by
  have hprod := linearIndependent_smul (hBrk k n μ₀ hanti)
    (pathProductLinearIndependent (GenField k n) n N isVec B μ₀)
  let φ : {x : PathIdx n N isVec B // x.1.1 N = μ₀} →
      {I : ℤ → Finset (Fin n) // IsStd μ₀ I} ×
        {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = μ₀ ∧ ∀ i, N < i → μ i = 0} :=
    fun x => (⟨x.1.1.2, by have := x.1.2.2.2; rw [x.2] at this; exact this⟩,
      ⟨x.1.1.1, x.1.2.1, x.2, x.1.2.2.1⟩)
  have hφ : Function.Injective φ := by
    intro x y h
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg (fun p => p.2.1) h
    exact Subtype.ext (Subtype.ext (Prod.ext h2 h1))
  have hc := hprod.comp φ hφ
  show LinearIndependent k (fun x : {x : PathIdx n N isVec B // x.1.1 N = μ₀} => fam k x.1)
  convert hc using 1
  funext x
  have hx : x.1.1.1 N = μ₀ := x.2
  show fam k x.1 = _
  unfold fam
  rw [hx]
  rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
