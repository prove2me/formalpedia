-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BaseGramNonnegativity.corT_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.11279+00:00
-- url     : https://prove2.me/submissions/e2afe463-ad24-4723-ba79-a9e287e34cce

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity
theorem _root_.solution : CorT := by
  intro E W _ D hG hW ε hε k Y T0 Th KK e Ws θ Mv Bmax Lhs he hMv hθ hTh hsum hL hB
  have key : ∀ w', ∑ t₀ ∈ T0, D.N0 ε k w' Y (Th t₀) ≤ (1 + e) * D.N0 ε k w' Y KK := by
    intro w'
    have h := baseGram_nonneg D hG hW hε k w' Y _ hsum
    have h2 := baseGram_sub D ε k w' Y (fun h h' => ∑ t₀ ∈ T0, Th t₀ h h')
      (fun h h' => ((1 + e : ℝ) : ℂ) * KK h h')
    have h3 : (fun h h' => (1 + (e : ℂ)) * KK h h' - ∑ t₀ ∈ T0, Th t₀ h h') =
        (fun h h' => ((1 + e : ℝ) : ℂ) * KK h h' - ∑ t₀ ∈ T0, Th t₀ h h') := by
      push_cast; rfl
    rw [h3, h2, baseGram_smul, baseGram_sum] at h
    linarith
  have hθ0 := hθ.1
  constructor
  · calc ∑ t₀ ∈ T0, Lhs t₀ ≤ ∑ t₀ ∈ T0, Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y (Th t₀) :=
          Finset.sum_le_sum hL
      _ = Mv * ∑ w' ∈ Ws, θ w' * ∑ t₀ ∈ T0, D.N0 ε k w' Y (Th t₀) := by
          rw [← Finset.mul_sum]; congr 1
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ Mv * ∑ w' ∈ Ws, θ w' * ((1 + e) * D.N0 ε k w' Y KK) := by
          apply mul_le_mul_of_nonneg_left _ hMv
          exact Finset.sum_le_sum (fun w' _ => mul_le_mul_of_nonneg_left (key w') (hθ0 w'))
      _ = (1 + e) * Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun _ _ => by ring)
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hMv)
    calc ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK ≤ ∑ w' ∈ Ws, θ w' * Bmax :=
          Finset.sum_le_sum (fun w' hw' => mul_le_mul_of_nonneg_left (hB w' hw') (hθ0 w'))
      _ = Bmax := by rw [← Finset.sum_mul, hθ.2.2, one_mul]
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
