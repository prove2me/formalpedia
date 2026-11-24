-- Prove2me | solution 1 for Formalism.L2.Th1.E.parallelogram_sum_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:58.595324+00:00
-- url     : https://prove2.me/submissions/719359a9-5b5b-4cc0-b26e-e15300160800

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
import Theorems.Thm_Formalism_L2_Th1_E_Power_sum_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
namespace Formalism.L2.Th1.E
theorem _root_.solution : ParSumTwo := by
  intro A _ _ M₀ m h
  have hm : ∀ Q : A, Q ≠ 0 → m Q = 0 := fun Q hQ => Power.sum_zero M₀ Q (m Q) fun P => h P Q hQ
  refine ⟨hm, ?_⟩
  have hpar : ∀ P Q : A, M₀ (P + Q) + M₀ (P - Q) = 2 * M₀ P := by
    intro P Q
    by_cases hQ : Q = 0
    · subst hQ; simp; ring
    · have := h P Q hQ
      rw [hm Q hQ] at this
      linarith
  have := Fintype.ofFinite A
  obtain ⟨P₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset A) M₀ ⟨0, Finset.mem_univ 0⟩
  have hconst : ∀ R : A, M₀ R = M₀ P₀ := by
    intro R
    have h1 := hpar P₀ (R - P₀)
    have h2 := hmax (P₀ + (R - P₀)) (Finset.mem_univ _)
    have h3 := hmax (P₀ - (R - P₀)) (Finset.mem_univ _)
    have e : P₀ + (R - P₀) = R := by abel
    rw [e] at h1 h2
    linarith
  intro P
  rw [hconst P, hconst 0]
end Formalism.L2.Th1.E
