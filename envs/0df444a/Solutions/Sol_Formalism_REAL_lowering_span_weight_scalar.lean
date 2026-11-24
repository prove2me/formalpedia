-- Prove2me | solution 1 for Formalism.REAL.lowering_span_weight_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:04.416048+00:00
-- url     : https://prove2.me/submissions/97bea380-821d-4467-a511-9daf3bef9054

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_height_functional_add
import Theorems.Thm_Formalism_REAL_height_word_shift_nonneg
import Theorems.Thm_Formalism_REAL_word_action_weight
import Theorems.Thm_Formalism_REAL_height_operator_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) {y : V}
    (hy : y ∈ lowSpan ε F x) (hyw : IsWeight F μ y) : ∃ c : ℂ, y = c • x := by
  set T := heightOperator F with hT
  set φ0 : ℂ := ((heightFunctional μ : ℝ) : ℂ) with hφ0
  have hle : lowSpan ε F x ≤ (ℂ ∙ x) ⊔ ⨆ l ∈ {l : ℂ | l ≠ φ0}, T.eigenspace l := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨w, hw, rfl⟩
    rcases w with _ | ⟨p, w⟩
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
    · apply Submodule.mem_sup_right
      have hwt := word_action_weight h hx.1 (p :: w) (fun q hq => (hw q hq).1)
      have hpos := (height_word_shift_nonneg (p :: w) (fun q hq => (hw q hq).2)).2 (List.cons_ne_nil _ _)
      have hmem : ew F (p :: w) x ∈ T.eigenspace ((heightFunctional (μ + wordWeightShift (p :: w)) : ℝ) : ℂ) := by
        rw [Module.End.mem_eigenspace_iff]; exact height_operator_weight hwt
      refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem ?_ hmem)
      show _ ≠ _
      rw [height_functional_add, hφ0]
      intro heq
      have := Complex.ofReal_injective heq
      linarith
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp (hle hy)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy1
  have hy2e : y2 ∈ T.eigenspace φ0 := by
    rw [Module.End.mem_eigenspace_iff]
    have e1 := height_operator_weight hyw
    have e2 := height_operator_weight hx.1
    rw [← hT, ← hφ0] at e1 e2
    rw [map_add, map_smul, e2, smul_add, smul_comm c φ0 x] at e1
    exact add_left_cancel e1
  have hdis := (Module.End.eigenspaces_iSupIndep T).disjoint_biSup
    (y := {l : ℂ | l ≠ φ0}) (x := φ0) (by simp)
  have : y2 = 0 := (Submodule.disjoint_def.mp hdis) y2 hy2e hy2
  exact ⟨c, by rw [this, add_zero]⟩
end Formalism.REAL
