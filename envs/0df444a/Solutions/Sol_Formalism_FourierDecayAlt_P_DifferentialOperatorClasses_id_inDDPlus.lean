-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.id_inDDPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:16:58.226281+00:00
-- url     : https://prove2.me/submissions/07035694-2439-42bd-8eaf-196abfb86e5d

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) : C6.InDDPlus D fib L 0 0 [idTerm k r Wp Wq] := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    constructor <;> intro g₀ _ <;>
      exact ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ _, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  · intro p _ f _ g _
    simp [B.opApply, B.Rw, B.rho, idTerm]
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, 0, [], ?_, ?_, by simp [idTerm], by simp, ?_⟩
    · exact ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
    · intro l _ _; exact ⟨rfl, rfl⟩
    · intro g _
      simp [C6.monoM, C6.Epart, idTerm]
      rfl
end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
