-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.pr_fst_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:49:25.843864+00:00
-- url     : https://prove2.me/submissions/646b31ca-a019-4b68-a339-8eeaaa765f36

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (s : Finset ι) (g : ι → Pr V) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  first
    | exact Prod.fst_sum (s := s) (f := g)
    | (classical
       induction s using Finset.induction_on with
       | empty => simp only [Finset.sum_empty]; rfl
       | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl)
end Formalism.FourierDecayAlt.P5
