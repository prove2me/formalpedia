-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.E2.mpd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:56.221206+00:00
-- url     : https://prove2.me/submissions/38159cf2-dd61-4b02-b021-4051e22d5b2d

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_smul__b5f706ad7ca8
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_bdd_sum__8f26d2801aec
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_E2_lim_sum__192f31adbb3d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.E2
open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory
namespace Formalism.FourierDecayAlt.P.E2
theorem _root_.solution : MeanPosDef := by
  intro Λ _ H _ _ LIM h1 h2 h3 h4 u B hu S c
  have hB : ∀ a b : Λ, Bdd (fun x => inner ℂ (u (x + a)) (u (x + b))) := fun a b =>
    ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul (hu _) (hu _) (norm_nonneg _) ((norm_nonneg _).trans (hu (x+a))))⟩
  have hB0 : ∀ b : Λ, Bdd (fun x => inner ℂ (u x) (u (x + b))) := fun b => by simpa using hB 0 b
  have e1 : ∀ σ σ' : Λ, LIM (fun x => inner ℂ (u x) (u (x + (σ - σ'))))
      = LIM (fun x => inner ℂ (u (x + σ')) (u (x + σ))) := by
    intro σ σ'
    rw [← h4 _ σ' (hB0 (σ - σ'))]
    congr 1; funext x; congr 2; abel
  have e2 : (∑ σ ∈ S, ∑ σ' ∈ S,
        LIM (fun x => inner ℂ (u x) (u (x + (σ - σ')))) * c σ * starRingEnd ℂ (c σ'))
      = LIM (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) := by
    rw [lim_sum' LIM h1 h2 S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lim_sum' LIM h1 h2 S _ (fun σ' => bdd_smul' _ (hB σ' σ))]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [h2 _ _ (hB σ' σ), e1]; ring
  rw [e2]
  apply h3
  · exact bdd_sum' S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))
  · intro x
    have key : (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) x
        = inner ℂ (∑ σ ∈ S, c σ • u (x + σ)) (∑ σ ∈ S, c σ • u (x + σ)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [key]
    exact ⟨inner_self_nonneg (𝕜 := ℂ), inner_self_im (𝕜 := ℂ) _⟩
end Formalism.FourierDecayAlt.P.E2
