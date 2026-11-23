-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.perp_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:07.180953+00:00
-- url     : https://prove2.me/submissions/fa4cd06d-40b0-4ae9-ac45-004ba3fb5379

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (T : Submodule ℂ (ι → ℂ)) (hT : T ≠ ⊤) : perp T ≠ ⊥ := by
  obtain ⟨f, hf, hle⟩ := T.exists_le_ker_of_lt_top hT.lt_top
  have hfx : ∀ x, f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  intro hb
  have hy : (star fun i => f (Pi.single i 1) : ι → ℂ) ∈ perp T := by
    intro x hx
    rw [star_star, ← hfx]
    exact hle hx
  rw [hb, Submodule.mem_bot, star_eq_zero] at hy
  apply hf
  refine LinearMap.ext fun x => ?_
  rw [hfx, hy]
  simp
end CompanionTheory.D.gk.admitted
