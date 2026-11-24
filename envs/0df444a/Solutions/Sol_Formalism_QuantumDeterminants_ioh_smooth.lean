-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:05:01.790151+00:00
-- url     : https://prove2.me/submissions/5fe789d4-608d-4de8-b6c8-3556885dfbe4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (hPQ : P * Q = 1)
    (hH : H = Pᴴ * Jm ε * P) (hf : SmoothOnH H f) : SmoothOnGV ε (fun x => f (Q * x * P)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf (Q * g₀ * P) (ioh_inUH ε H P Q g₀ hPQ hH hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.mulLeft ℝ Q).comp (LinearMap.mulRight ℝ P)).toContinuousLinearMap
  have hL : ∀ x, L x = Q * x * P := by
    intro x; simp [L, Matrix.mul_assoc]
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hg₀U, ?_, ?_⟩
  · exact hF.comp L.contDiff.contDiffOn (fun x hx => hx)
  · intro x hx hxJ
    simp only [Set.mem_preimage, hL] at hx
    simp only [hL]
    exact hfF _ hx (ioh_inUH ε H P Q x hPQ hH hxJ)
end Formalism.QuantumDeterminants
