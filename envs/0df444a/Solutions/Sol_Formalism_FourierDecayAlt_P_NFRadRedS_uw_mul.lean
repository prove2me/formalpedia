-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:11.543923+00:00
-- url     : https://prove2.me/submissions/cad7de3b-6245-483c-bb38-32bc32850924

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {g h : Q.Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) :
    g * h ∈ UWset k r z := by
  obtain ⟨hu, hb, hz⟩ := hg
  obtain ⟨hu', hb', hz'⟩ := hh
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    have e1 : gᴴ * Hpk k r * g = Hpk k r := hu
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hu'
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · rw [← Matrix.mulVec_mulVec, (hb' a).1, (hb a).1]
  · rw [← Matrix.mulVec_mulVec, (hb' a).2, (hb a).2]
  · rw [← Matrix.mulVec_mulVec, hz', hz]
end Formalism.FourierDecayAlt.P.NFRadRedS
