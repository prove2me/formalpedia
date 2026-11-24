-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.GaussB.norm_det_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:06:19.888719+00:00
-- url     : https://prove2.me/submissions/c5e87e1b-0ef4-499d-a9f4-c76c0eac43ae

import Definitions.Def_Formalism_GaussJetBounds_StatementY
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.GaussB
namespace Formalism.DworkPowerSeriesWeights.GaussB
theorem _root_.solution {K : Type} [NormedField K] {T : Type} {N0 : ℕ} (p : ℕ) [Fact p.Prime]
    (Y : T × Fin N0 × Fin N0 → K) (hY : IsGeneric p Y) (τ : T) :
    ‖(Matrix.of fun i a : Fin N0 => Y (τ, i, a)).det‖ = 1 := by
  classical
  set M : Matrix (Fin N0) (Fin N0) (MvPolynomial (T × Fin N0 × Fin N0) ℤ) :=
    Matrix.of fun i a => MvPolynomial.X (τ, i, a) with hM
  have h1 : (Matrix.of fun i a : Fin N0 => Y (τ, i, a)).det = MvPolynomial.aeval Y M.det := by
    rw [AlgHom.map_det]
    congr 1
    ext i a
    simp [hM]
  rw [h1]
  refine hY _ fun h0 => ?_
  set ψ : MvPolynomial (T × Fin N0 × Fin N0) ℤ →+* ZMod p :=
    (MvPolynomial.eval (fun y : T × Fin N0 × Fin N0 => if y.2.1 = y.2.2 then (1 : ZMod p) else 0)).comp
      (MvPolynomial.map (Int.castRingHom (ZMod p))) with hψ
  have h2 : ψ M.det = 0 := by
    rw [hψ, RingHom.comp_apply, h0, map_zero]
  rw [RingHom.map_det] at h2
  have h3 : ψ.mapMatrix M = 1 := by
    ext i a
    simp [hM, hψ, Matrix.one_apply]
  rw [h3, Matrix.det_one] at h2
  exact one_ne_zero h2
end Formalism.DworkPowerSeriesWeights.GaussB
