-- Prove2me | solution 1 for Formalism.REAL.group_exponential_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:58:01.692294+00:00
-- url     : https://prove2.me/submissions/55a6862a-2f94-44c9-8cb9-1542863ce266

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst
import Theorems.Thm_Formalism_REAL_continuous_exp_real_smul
import Theorems.Thm_P2M_Formalism_REAL_toM_injective__bc4491a48ce7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory MeasureTheory.Measure
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : ExpGFacts := by
  intro n ε X hX
  have hE : ∀ t : ℝ, toM (expG ε X t) = NormedSpace.exp ((t : ℂ) • X) := fun t => toM_expG ε X t hX
  have hcont : Continuous (fun t : ℝ => expG ε X t) := by
    have hcU : Continuous (fun t : ℝ => ((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
      rw [Units.continuous_iff]
      refine ⟨?_, ?_⟩
      · have h1 : (Units.val ∘ fun t : ℝ => ((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) =
            fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := funext hE
        rw [h1]
        exact continuous_exp_real_smul X
      · have h2 : (fun t : ℝ => ((((expG ε X t : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ :
            (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
            fun t : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • X) := by
          funext t
          apply Units.inv_eq_of_mul_eq_one_right
          show toM (expG ε X t) * _ = 1
          rw [hE, ← Matrix.exp_add_of_commute _ _
            (((Commute.refl X).smul_left ((t : ℝ) : ℂ)).smul_right (((-t : ℝ)) : ℂ)), ← add_smul]
          push_cast
          rw [add_neg_cancel, zero_smul, NormedSpace.exp_zero]
        rw [h2]
        exact (continuous_exp_real_smul X).comp continuous_neg
    exact continuous_induced_rng.2 hcU
  refine ⟨?_, ?_, hcont, ?_⟩
  · apply toM_injective'
    rw [hE]
    simp
    rfl
  · intro s t
    apply toM_injective'
    show toM (expG ε X (s + t)) = toM (expG ε X s) * toM (expG ε X t)
    rw [hE, hE, hE, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl X).smul_left ((s : ℝ) : ℂ)).smul_right ((t : ℝ) : ℂ))]
    congr 1
    push_cast
    rw [add_smul]
  · intro hK
    have hk : ∀ t : ℝ, ((expK ε X t : KG ε) : UJ ε) = expG ε X t := by
      intro t
      unfold expK
      rw [dif_pos hK]
    refine ⟨hk, ?_⟩
    apply continuous_induced_rng.2
    have h3 : (Subtype.val ∘ fun t : ℝ => expK ε X t) = fun t : ℝ => expG ε X t := funext hk
    rw [h3]
    exact hcont
end Formalism.REAL
