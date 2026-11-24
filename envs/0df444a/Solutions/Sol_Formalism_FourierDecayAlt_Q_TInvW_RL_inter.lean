-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.RL_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:17.710084+00:00
-- url     : https://prove2.me/submissions/1c9fd47f-105d-4a59-9683-5a1158ca6bc6

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD
variable {s' : Mx k r} (hs' : ∀ g ∈ Glev k r i ∩ D, g * s' ∈ Glev k r i ∩ D)
variable (hRS : StepRSm) (hs'G : s' ∈ Glev k r i)
include hRS hs'G
variable (hRt : StepRight)
include hRt
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (a b : Fin (mdim k r i)) :
    Ealg (E := E) hP hC hD a b * RL (E := E) hP hC hD hs' hRS hs'G =
      RL (E := E) hP hC hD hs' hRS hs'G * Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b := by
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have hcon := hC E k r i D a b (ext k r i D (Rf hs' x.1)) (fun y => ext k r i D x.1 (y * s')) g hD hg
    (fun y hy => by
      show ext k r i D (Rf hs' x.1) y = ext k r i D x.1 (y * s')
      rw [ext_at hy, ext_at (hs' y hy)]
      rfl)
  have hR := hRt E k r i D a b (ext k r i D x.1) s' g hD x.2 hs'G hg.1 (hs' g hg).2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (Rf hs' x.1)) g =
    (Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b x).1 ⟨g * s', hs' g hg⟩
  rw [hcon, hR]
  simp only [Econj, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  rfl
end Formalism.FourierDecayAlt.Q.TInvW
