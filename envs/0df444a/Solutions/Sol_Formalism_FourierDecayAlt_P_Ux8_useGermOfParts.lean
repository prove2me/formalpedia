-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.useGermOfParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:42:12.397803+00:00
-- url     : https://prove2.me/submissions/c638e48b-b39f-4c7a-adcd-b2b34319c907

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
private theorem nonneg_of_CCle_mat {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {f : B.Mat k r → E} {c : ℝ} (hf : B.CCle A m f c) : 0 ≤ c := by
  have h1 : (1 : B.Mat k r) ∈ B.GV k r := by
    show (1 : B.Mat k r)ᴴ * _ * 1 = _
    simp
  obtain ⟨_, h2⟩ := hf
  have h := h2 [] [] (by simp) (by simp) (by simp) 1 h1
  exact le_trans (mul_nonneg (Real.rpow_nonneg (by unfold B.gN; exact Real.sqrt_nonneg _) _) (norm_nonneg _)) h
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
theorem _root_.solution : UseGermOfParts := by
  intro hG hD hC hDB hPM hSM
  obtain ⟨C₁, C₂, hGR⟩ := hG
  obtain ⟨Cc, hCc⟩ := hC C₁ C₂
  refine ⟨C₂, Cc, ?_⟩
  intro k p m ρ Wp Wq _ _ _ _ _ _ ι _ U hU A₀ hA₀
  obtain ⟨_, twice_smooth_le_first, hAB, C, hCf⟩ := hCc k p (m + 1 + 1) ρ Wp Wq ι U hU A₀ hA₀
  refine ⟨hAB, ?_⟩
  intro Kc hKc h0
  obtain ⟨_, hβ, _⟩ := hSM
  obtain ⟨Cst, hCst⟩ := hGR m betaU hβ Kc hKc h0
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  refine ⟨max R 0 ^ (Mlev k ρ - 2) * Cst * max C 0, ?_⟩
  intro f c hf V _ _ _ M
  have hc0 : 0 ≤ c := nonneg_of_CCle_mat hf
  obtain ⟨Φ, hev, hbd⟩ := hCf f c hf V M
  refine ⟨Φ, hev, ?_⟩
  intro t D ht hD'
  have hA' : (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ U.a C₂ A₀ := by
    have e : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    rw [e] at twice_smooth_le_first
    exact twice_smooth_le_first
  have hA0 : 0 ≤ U.a C₂ A₀ := le_trans (by positivity) hA'
  have hK0 : 0 ≤ max C 0 * c := mul_nonneg (le_max_right _ _) hc0
  have hDB' : G.DerivBound (C₂ * (m + 1 + 1) ^ 2) (G.detSet (m + 1) Kc)
      (fun Z => max C 0 * c * min 1 (‖Z‖ ^ (-(U.a C₂ A₀)))) Φ := by
    refine hDB (m + 1 + 1) (C₂ * (m + 1 + 1) ^ 2) V Φ (U.a C₂ A₀) (max C 0 * c) (G.detSet (m + 1) Kc)
      (by omega) hA0 hK0 (zero_notMem_detSet hD (m + 1) Kc h0) ?_
    intro Z hZ
    obtain ⟨hcd, hb⟩ := hbd Z hZ
    refine ⟨hcd, fun q hq => le_trans (hb q hq) ?_⟩
    have hr : 0 ≤ (1 + ‖Z‖) ^ (-(U.a C₂ A₀)) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0) hr
  have h2 : 2 ≤ Mlev k ρ := by unfold Mlev; omega
  have hDR : ‖D‖ ≤ max R 0 := le_trans (hR D hD') (le_max_left R 0)
  have hpow : ‖D‖ ^ (Mlev k ρ - 2) ≤ max R 0 ^ (Mlev k ρ - 2) := by gcongr
  have hrem := hCst V Φ (U.a C₂ A₀) (max C 0 * c) (C₂ * (m + 1 + 1) ^ 2) hA' (le_of_eq (by ring)) hDB' t
    (D / t ^ (m + 1)) ht (by rw [div_mul_cancel₀ _ (pow_ne_zero _ ht)]; exact hD')
  rw [hPM m (Mlev k ρ) betaU t D V Φ h2 ht, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖D‖ ^ (Mlev k ρ - 2) * ‖G.remainder betaU m (fun _ => 1) Φ t (D / t ^ (m + 1))‖
      ≤ max R 0 ^ (Mlev k ρ - 2) * (Cst * (max C 0 * c) * ‖t‖) :=
        mul_le_mul hpow hrem (norm_nonneg _) (pow_nonneg (le_max_right R 0) _)
    _ = max R 0 ^ (Mlev k ρ - 2) * Cst * max C 0 * c * ‖t‖ := by ring
end Formalism.FourierDecayAlt.P.Ux8
