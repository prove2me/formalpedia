-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Kf_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:24:20.851847+00:00
-- url     : https://prove2.me/submissions/35980856-eaa1-4d26-a33b-b387a226e353

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {T : Q → Q → ℂ} (hT : (Matrix.of T).PosDef ∧ (Matrix.trace (Matrix.of T)).re ≤ 1) (σ : ℝ) :
    (fun B : Q → P → ℂ => Kf P Q σ (T, B)) = (Sl P T σ).indicator 1 := by
  funext B
  by_cases hB : qf (Matrix.of T) (cm B) ≤ σ ^ 2
  · have h1 : (T, B) ∈ Kset P Q σ := by
      simp only [Kset, Set.mem_setOf_eq]; exact ⟨hT.1, hT.2, hB⟩
    have h2 : B ∈ Sl P T σ := by
      simp only [Sl, Set.mem_setOf_eq]; exact hB
    unfold Kf
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    all_goals rfl
  · have h1 : (T, B) ∉ Kset P Q σ := by
      simp only [Kset, Set.mem_setOf_eq]; exact fun h => hB h.2.2
    have h2 : B ∉ Sl P T σ := by
      simp only [Sl, Set.mem_setOf_eq]; exact hB
    unfold Kf
    first
    | rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    | rw [Set.indicator_of_not_mem h1, Set.indicator_of_not_mem h2]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
