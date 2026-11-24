-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:25.064066+00:00
-- url     : https://prove2.me/submissions/16243f7c-7db6-4b7f-a128-7ea787c19dc1

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_sv_stepV
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_top_coeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_top_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) :
    ∀ (L : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (w : Vs), SV σ w →
      SV σ (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w) ∧
      ∀ g ∈ GV k r, (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 p.2.1 p.2.2).foldr (fun T h => T h) (fun x => ℓ (σ x w)) g =
        ℓ (σ g (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w)) := by
  intro L
  induction L with
  | nil => intro w hw; exact ⟨hw, fun g _ => rfl⟩
  | cons p L ih =>
    intro w hw
    obtain ⟨h1, h2⟩ := ih w hw
    refine ⟨sv_stepV hrep h1 _ _ _, fun g hg => ?_⟩
    simp only [List.map_cons, List.foldr_cons]
    rw [top_local (f' := fun x => ℓ (σ x (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w))) h2 _ _ _ hg]
    exact top_coeff hrep h1 ℓ _ _ _ hg
end Formalism.FourierDecayAlt.P.Qb1
