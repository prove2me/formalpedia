-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.phiMat_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:57.480897+00:00
-- url     : https://prove2.me/submissions/6b6ff0de-a1b9-4cd0-a2d2-c84e0ff63713

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution [IsDomain O] (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type}
    [Fintype g] [DecidableEq g] (Θ : Matrix g g R') (x' : X') :
    (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det =
      (-1) ^ Fintype.card (g × d) *
        PowerSeries.coeff (Fintype.card (g × d)) (phiMat R' Θ).det x' := by
  classical
  have hL : PowerSeries.coeff (Fintype.card (g × d)) (phiMat R' Θ).det x' =
      PowerSeries.coeff (Fintype.card (g × d))
        ((PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix (phiMat R' Θ)).det := by
    rw [← RingHom.map_det, PowerSeries.coeff_map]
    rfl
  have hM : (PowerSeries.map (Pi.evalRingHom (fun _ : X' => FractionRing O) x')).mapMatrix (phiMat R' Θ) =
      (Polynomial.coeToPowerSeries.ringHom).mapMatrix
        (1 - (Polynomial.X : Polynomial (FractionRing O)) •
          (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).map Polynomial.C) := by
    ext P Q
    by_cases hPQ : P = Q <;>
      simp [phiMat, bigMat, Matrix.one_apply, hPQ, Polynomial.coe_X, Polynomial.coe_C] <;> ring
  rw [hL, hM, ← RingHom.map_det]
  rw [show (Polynomial.coeToPowerSeries.ringHom : Polynomial (FractionRing O) →+* PowerSeries (FractionRing O))
      (Matrix.det (1 - (Polynomial.X : Polynomial (FractionRing O)) •
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).map Polynomial.C)) =
      (((bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).charpolyRev :
        Polynomial (FractionRing O)) : PowerSeries (FractionRing O)) from rfl]
  rw [Polynomial.coeff_coe, ← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le (le_refl _), Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff]
end Formalism.NG.BlockDetAlt
