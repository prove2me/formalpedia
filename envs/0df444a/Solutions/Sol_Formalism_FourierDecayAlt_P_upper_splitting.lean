-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.upper_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:55.526805+00:00
-- url     : https://prove2.me/submissions/59287bd6-0bd5-4155-bef7-4c1d1f3c5117

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting
import Theorems.Thm_Formalism_FourierDecayAlt_P_lower_triangular_splitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P
namespace InverseSplitting
open C2x2
variable {m : ℕ}
end InverseSplitting
open C2x2 InverseSplitting
private lemma conjTranspose_mem_ltset_of_mem_utset {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ C2.UTset m) :
    vᴴ ∈ C2.LTset m :=
  ⟨fun i j h => by simp [Matrix.conjTranspose_apply, hv.1 j i h],
    fun i => by simp [Matrix.conjTranspose_apply, hv.2 i]⟩
private lemma conjTranspose_mem_utset_of_mem_ltset {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ C2.LTset m) :
    vᴴ ∈ C2.UTset m :=
  ⟨fun i j h => by simp [Matrix.conjTranspose_apply, hv.1 j i h],
    fun i => by simp [Matrix.conjTranspose_apply, hv.2 i]⟩
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 InverseSplitting
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.UpSplit := by
  intro m P hP u hu
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, huniq⟩ := lower_triangular_splitting m P hP uᴴ (conjTranspose_mem_ltset_of_mem_utset hu)
  refine ⟨(bᴴ, aᴴ), ⟨conjTranspose_mem_utset_of_mem_ltset hb.1, conjTranspose_mem_utset_of_mem_ltset ha.1,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hb,
    by simpa only [Matrix.conjTranspose_conjTranspose] using ha, ?_⟩, ?_⟩
  · have hab' : uᴴ = a * b := hab
    show u = bᴴ * aᴴ
    rw [← Matrix.conjTranspose_mul, ← hab', Matrix.conjTranspose_conjTranspose]
  · rintro ⟨q1, q2⟩ ⟨_, _, hq1c, hq2c, hq⟩
    have hq' : u = q1 * q2 := hq
    have h := huniq (q2ᴴ, q1ᴴ) ⟨hq2c, hq1c, by
      show uᴴ = q2ᴴ * q1ᴴ
      rw [← Matrix.conjTranspose_mul, ← hq']⟩
    simp only [Prod.mk.injEq] at h
    rw [← h.1, ← h.2, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
end Formalism.FourierDecayAlt.P
