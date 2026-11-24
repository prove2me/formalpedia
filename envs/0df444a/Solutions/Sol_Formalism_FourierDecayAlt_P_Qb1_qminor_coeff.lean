-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.qminor_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:46:52.555797+00:00
-- url     : https://prove2.me/submissions/ae7ce9e1-3ce1-49b7-ba98-0d309d88abad

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_steps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {w : Vs} (hw : SV σ w) {g : Mx k r} (hg : g ∈ GV k r) :
    qminorOp (EH k r) a b u (fun x => ℓ (σ x w)) g =
      ℓ (σ g (qmF (fun a b => EcRep (Hpk k r) σ (Matrix.single a b 1)) a b u w)) := by
  unfold qminorOp qmF
  rw [Finset.sum_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Pi.smul_apply, map_smul, map_smul]
  congr 1
  have e1 : (List.ofFn fun i : Fin t => QuantumDeterminants.Top (EH (E := ℂ) k r) (u - ((i : ℕ) : ℂ)) (a (τ i)) (b i)) =
      (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).map
        (fun p => QuantumDeterminants.Top (EH (E := ℂ) k r) p.1 p.2.1 p.2.2) := by
    rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun i : Fin t => fun y : Vs =>
      (if a (τ i) = b i then (u - ((i : ℕ) : ℂ)) • y else 0) +
        EcRep (Hpk k r) σ (Matrix.single (a (τ i)) (b i) 1) y).foldr (fun T h => T h) w =
      (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).foldr
        (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w := by
    have e3 : (List.ofFn fun i : Fin t => fun y : Vs =>
        (if a (τ i) = b i then (u - ((i : ℕ) : ℂ)) • y else 0) +
          EcRep (Hpk k r) σ (Matrix.single (a (τ i)) (b i) 1) y) =
        (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).map
          (fun (p : ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (y : Vs) => stepV σ p.1 p.2.1 p.2.2 y) := by
      rw [List.map_ofFn]; rfl
    rw [e3, List.foldr_map]
  rw [e1, e2]
  exact (steps hrep ℓ _ w hw).2 g hg
end Formalism.FourierDecayAlt.P.Qb1
