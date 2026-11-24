-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.AL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:45.833017+00:00
-- url     : https://prove2.me/submissions/cedb53df-0986-41b5-86c2-e0b540075640

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_tuo_smulRight_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {Ω : Set 𝔤} (hΩ : IsOpen Ω) (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ))
    (ha : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a i) Ω) (B : ℝ) (hB : ∀ i, ∀ Y ∈ Ω, ‖a i Y‖ ≤ B) :
    ∀ (m : ℕ) (Ψ : List ι → ℕ → 𝔤 → E) (L : List ι → 𝔤 → E),
      (∀ w : List ι, w.length ≤ m → ∀ n, ContinuousOn (Ψ w n) Ω) →
      (∀ w : List ι, w.length < m → ∀ n, ∀ Y ∈ Ω,
        HasFDerivAt (Ψ w n) (∑ i, (a i Y).smulRight (Ψ (i :: w) n Y)) Y) →
      (∀ w : List ι, w.length ≤ m → TendstoUniformlyOn (Ψ w) (L w) atTop Ω) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (L []) Ω := by
  intro m
  induction m with
  | zero =>
    intro Ψ L hc _ hu
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hu [] le_rfl).continuousOn (Filter.Frequently.of_forall fun n => hc [] le_rfl n)
  | succ m ih =>
    intro Ψ L hc hd hu
    have hL : ∀ j : ι, ContDiffOn ℝ (m : WithTop ℕ∞) (L [j]) Ω := by
      intro j
      have := ih (fun w => Ψ (w ++ [j])) (fun w => L (w ++ [j]))
        (fun w hw n => hc _ (by simp; omega) n)
        (fun w hw n Y hY => by simpa using hd (w ++ [j]) (by simp; omega) n Y hY)
        (fun w hw => hu _ (by simp; omega))
      simpa using this
    have hder : ∀ Y ∈ Ω, HasFDerivAt (L []) (∑ i, (a i Y).smulRight (L [i] Y)) Y := by
      intro Y hY
      exact hasFDerivAt_of_tendstoUniformlyOn hΩ
        (tuo_smulRight_sum a B hB (fun i => Ψ [i]) (fun i => L [i]) (fun i => hu [i] (by simp)))
        (fun n Y hY => hd [] (by simp) n Y hY) (fun Y hY => (hu [] (by simp)).tendsto_at hY) hY
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun Y hY => (hder Y hY).differentiableAt.differentiableWithinAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · have hcd : ContDiffOn ℝ (m : WithTop ℕ∞) (fun Y => ∑ i, (a i Y).smulRight (L [i] Y)) Ω :=
        ContDiffOn.sum fun i _ => ((ha i).of_le (by exact_mod_cast le_top)).smulRight (hL i)
      exact hcd.congr fun Y hY => (hder Y hY).fderiv
end Formalism.FourierDecayAlt.P.Ux1
