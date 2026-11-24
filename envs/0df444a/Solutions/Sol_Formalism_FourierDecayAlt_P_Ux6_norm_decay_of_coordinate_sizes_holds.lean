-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.norm_decay_of_coordinate_sizes_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:39:34.593116+00:00
-- url     : https://prove2.me/submissions/f21f2200-4a4c-4731-b11d-d58ce64969c3

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution : CoordinateDecayOfSizes := by
  intro h21 k p s ρ σ d hd hs K hK hK0 A' hA'
  obtain ⟨C, hC⟩ := h21 k p s ρ σ d hd hs K hK hK0
  set C1 := max C 1 with hC1
  have hC1pos : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set N : ℕ := 2 * (p + s + ρ) + 1 with hN
  have hpos : 0 < 8 * (2 * ((p + s + ρ : ℕ) : ℝ) + 1) := by positivity
  set e : ℝ := -(A' / (8 * (2 * ((p + s + ρ : ℕ) : ℝ) + 1))) with he
  have he0 : e ≤ 0 := by
    have := div_nonneg hA' hpos.le
    linarith
  refine ⟨(C1 ^ 8) ^ (-e), ?_⟩
  intro ξ Z γ hγ hD
  obtain ⟨hg1, -, -, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hC ξ Z γ hγ hD
  set g := B.gN (gaXi k ρ σ d ξ Z γ) with hg
  have hgpos : 0 < g := by linarith
  have up : ∀ (x : ℝ) (m : ℕ), m ≤ N → x ≤ C * g ^ m → x ≤ C1 * g ^ N := by
    intro x m hm hx
    have h1' : g ^ m ≤ g ^ N := pow_le_pow_right₀ hg1 hm
    have h0 : 0 ≤ g ^ m := by positivity
    calc x ≤ C * g ^ m := hx
      _ ≤ C1 * g ^ m := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ C1 * g ^ N := mul_le_mul_of_nonneg_left h1' hC1pos.le
  have hγpos : 0 < B.gN γ := BetaSesquilinearity.gN_pos hγ
  set M := C1 * g ^ N with hM
  have e1 := up _ _ (by omega) h1
  have e2 := up _ _ (by omega) h2
  have e3 := up _ _ (by omega) h3
  have e4 := up _ _ (by omega) h4
  have e5 := up _ _ (by omega) h5
  have e6 := up _ _ (by omega) h6
  have e7 := up _ _ (by omega) h7
  have e8 := up _ _ (by omega) h8
  have hPpos : 0 < wt ξ * (1 + ‖Z‖) * B.gN γ := by
    simp only [wt, wtH]; positivity
  have hP : wt ξ * (1 + ‖Z‖) * B.gN γ ≤ M ^ 8 := by
    simp only [wt, wtH]
    calc (1 + ‖ξ.1.1‖) * (1 + ‖ξ.1.2‖) *
          ((1 + ‖ξ.2.1.1‖) * (1 + ‖ξ.2.1.2‖) * (1 + ‖ξ.2.2.1‖) * (1 + ‖ξ.2.2.2‖)) * (1 + ‖Z‖) * B.gN γ
        ≤ M * M * (M * M * M * M) * M * M := by
          gcongr
      _ = M ^ 8 := by ring
  have key : (M ^ 8) ^ e ≤ (wt ξ * (1 + ‖Z‖) * B.gN γ) ^ e := Real.rpow_le_rpow_of_nonpos hPpos hP he0
  have hNr : ((8 * N : ℕ) : ℝ) * e = -A' := by
    rw [he, hN]; push_cast; field_simp
  have hM8 : (M ^ 8) ^ e = (C1 ^ 8) ^ e * g ^ (-A') := by
    rw [show M ^ 8 = C1 ^ 8 * g ^ (8 * N) by rw [hM]; ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hgpos.le, hNr]
  have hC8 : 0 < C1 ^ 8 := by positivity
  calc g ^ (-A') = (C1 ^ 8) ^ (-e) * (M ^ 8) ^ e := by
        rw [hM8, ← mul_assoc, Real.rpow_neg hC8.le, inv_mul_cancel₀ (by positivity), one_mul]
    _ ≤ (C1 ^ 8) ^ (-e) * (wt ξ * (1 + ‖Z‖) * B.gN γ) ^ e :=
        mul_le_mul_of_nonneg_left key (by positivity)
end Formalism.FourierDecayAlt.P.Ux6
