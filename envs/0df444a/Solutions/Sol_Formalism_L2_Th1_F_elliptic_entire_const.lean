-- Prove2me | solution 1 for Formalism.L2.Th1.F.elliptic_entire_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:52.442739+00:00
-- url     : https://prove2.me/submissions/05bb3641-8abc-4d24-9317-359f6dc80d4b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : EllipticEntire := by
  intro L f hf hper z
  have key : ∀ x : ℂ, ∃ ω ∈ L.lattice, ‖x - ω‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := by
    intro x
    have hx := L.basis.sum_repr x
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hx
    refine ⟨(⌊L.basis.repr x 0⌋ : ℂ) * L.ω₁ + (⌊L.basis.repr x 1⌋ : ℂ) * L.ω₂,
      PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, ?_⟩
    generalize L.basis.repr x 0 = a at hx ⊢
    generalize L.basis.repr x 1 = b at hx ⊢
    subst hx
    have e : a • L.ω₁ + b • L.ω₂ - ((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂)
        = ((Int.fract a : ℝ) : ℂ) * L.ω₁ + ((Int.fract b : ℝ) : ℂ) * L.ω₂ := by
      simp only [Complex.real_smul, Int.fract]; push_cast; ring
    rw [e]
    have hfr : ∀ (r : ℝ) (v : ℂ), ‖((Int.fract r : ℝ) : ℂ) * v‖ ≤ ‖v‖ := by
      intro r v
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    exact (norm_add_le _ _).trans (add_le_add (hfr a _) (hfr b _))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (‖L.ω₁‖ + ‖L.ω₂‖)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hb : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨ω, hω, hxω⟩ := key x
    have : f x = f (x - ω) := by
      have := hper ω hω (x - ω)
      rwa [sub_add_cancel] at this
    rw [this]
    exact hC _ (by simpa using hxω)
  exact hf.apply_eq_apply_of_bounded hb z 0
end Formalism.L2.Th1.F
