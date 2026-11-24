-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT.span_short_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:15.318139+00:00
-- url     : https://prove2.me/submissions/7602bdc1-e720-44fc-9f6e-5b0f972c5949

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceCover
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PLemTGeo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) (μ : ℝ) (hμ : 0 < μ) (hcov : ∀ x : W, ∃ l ∈ Λ, ‖x - l‖ ≤ μ) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ} = ⊤ := by
  set K := Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ} with hK
  by_contra hne
  have hKo : Kᗮ ≠ ⊥ := by
    intro h
    exact hne (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set x : W := (2 * μ / ‖u‖) • u with hx
  have hxn : ‖x‖ = 2 * μ := by
    rw [hx, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hxK : x ∈ Kᗮ := Submodule.smul_mem _ _ hu
  obtain ⟨l, hl, hd⟩ := hcov x
  have hln : ‖l‖ ≤ 3 * μ := by
    have : ‖l‖ ≤ ‖x‖ + ‖x - l‖ := by
      calc ‖l‖ = ‖x - (x - l)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
    linarith
  have hlK : l ∈ K := Submodule.subset_span ⟨hl, hln⟩
  have horth : ⟪l, x⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hlK hxK
  have hsq : ‖x - l‖ ^ 2 = ‖x‖ ^ 2 + ‖l‖ ^ 2 := by
    rw [@norm_sub_sq_real, real_inner_comm, horth]
    ring
  have h1 : ‖x - l‖ ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  nlinarith [sq_nonneg ‖l‖]
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
