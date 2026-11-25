-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.mem_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:08:13.429991+00:00
-- url     : https://prove2.me/submissions/22c1d14a-5d8b-4681-9e03-9188a2f3ab0c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh.1, hgG.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hgG.2 a ha).1, (hgG.2 a ha).2]
      exact hh.2.1 a
  · have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ h ⟨h, hh, 1, h1N, by simp⟩ 1 ⟨1, h1z', 1, h1N, by simp⟩
    simpa using hS
end Formalism.FourierDecayAlt.P.QrD
