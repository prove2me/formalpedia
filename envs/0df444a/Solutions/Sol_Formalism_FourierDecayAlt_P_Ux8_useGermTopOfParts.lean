-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.useGermTopOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:29.114083+00:00
-- url     : https://prove2.me/submissions/a7c788a8-3f81-49f3-addd-f834714e884d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_zero_notMem_detSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux8
private theorem nonneg_of_decayAll {N : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {q : ℕ} {e : ℕ → ℝ} {K : ℝ} {Φ0 : G.Mat N → V} (h : DecayAll q e K Φ0) : 0 ≤ K := by
  obtain ⟨_, hb⟩ := h
  have h1 := hb 0 (Nat.zero_le _) 0
  rw [norm_zero, add_zero, Real.one_rpow, mul_one] at h1
  exact le_trans (norm_nonneg _) h1
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (p : Seminorm ℂ V)
end
section supp
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pi
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
end pi
end supp
end Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution : UseGermTopOfParts := by
  intro hG hD hTC hDB
  obtain ⟨C₁, C₂, hGR⟩ := hG
  refine ⟨C₁, C₂, ?_⟩
  intro p m β hβ σ d hd e A hA he Kc hKc h0
  obtain ⟨Cst₁, hC₁⟩ := hTC p (m + 1 + 1) β σ d hd (by omega) (C₂ * (m + 2) ^ 2) e (fun i hi => (he i hi).2)
  obtain ⟨Cst₂, hC₂⟩ := hGR m β hβ Kc hKc h0
  refine ⟨Cst₂ * Cst₁, ?_⟩
  intro V _ _ _ Φ0 K hΦ t c ht hc
  have hT := (hC₁ V Φ0 K hΦ).2
  have hK : 0 ≤ Cst₁ * K := nonneg_of_decayAll hT
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hDB' : G.DerivBound (C₂ * (m + 2) ^ 2) (G.detSet (m + 1) Kc)
      (fun Z => Cst₁ * K * min 1 (‖Z‖ ^ (-A))) (PhiTop β σ d Φ0) := by
    refine hDB (m + 1 + 1) (C₂ * (m + 2) ^ 2) V (PhiTop β σ d Φ0) A (Cst₁ * K) (G.detSet (m + 1) Kc)
      (by omega) hA0 hK (zero_notMem_detSet hD (m + 1) Kc h0) ?_
    intro Z _
    obtain ⟨hcd, hb⟩ := hT
    refine ⟨hcd.contDiffAt, fun q hq => ?_⟩
    have h1 := hb q hq Z
    have hZ : (1 : ℝ) ≤ 1 + ‖Z‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hexp : (1 + ‖Z‖) ^ (-(e q / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)))) ≤ (1 + ‖Z‖) ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg (he q hq).1)
    calc _ ≤ _ := h1
      _ ≤ Cst₁ * K * (1 + ‖Z‖) ^ (-A) := mul_le_mul_of_nonneg_left hexp hK
  have hfin := hC₂ V (PhiTop β σ d Φ0) A (Cst₁ * K) (C₂ * (m + 2) ^ 2) hA le_rfl hDB' t c ht hc
  calc _ ≤ Cst₂ * (Cst₁ * K) * ‖t‖ := hfin
    _ = Cst₂ * Cst₁ * K * ‖t‖ := by ring
end Formalism.FourierDecayAlt.P.Ux8
