-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:05.366872+00:00
-- url     : https://prove2.me/submissions/b44d28d9-a0e2-4243-8dbc-e59024659fd3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
private theorem isUnit_det_of_mem_uwset {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) :
    IsUnit g.det := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg.1
  have hH : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h2
  rw [← h2] at hH
  simp at hH
end Formalism.FourierDecayAlt.P.NFRadRedS
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.NFRadRedS
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul g (isUnit_det_of_mem_uwset hg)
end Formalism.FourierDecayAlt.P.NFRadRedS
