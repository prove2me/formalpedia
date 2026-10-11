-- Prove2me | solution 1 for FredholmBanach.isFredholm_add_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:29:26.789247+00:00
-- url     : https://prove2.me/submissions/35475fe3-5e65-4112-b731-5fda3106a766

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional
import Theorems.Thm_FredholmBanach_compact_perturbation_ker_range
import Theorems.Thm_FredholmBanach_compact_perturbation_coker
import Theorems.Thm_FredholmBanach_isOpen_isFredholm_index_locallyConstant
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.LocallyConstant.Basic

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {u h : E →L[𝕜] F} (hu : u.IsFredholm) (hh : IsCompactOperator h) :
    (u + h).IsFredholm ∧ FredholmBanach.index (u + h) = FredholmBanach.index u := by
  -- every `u + h'` with `h'` compact is Fredholm
  have hF : ∀ h' : E →L[𝕜] F, IsCompactOperator h' → (u + h').IsFredholm := by
    intro h' hh'
    have hk := (FredholmBanach.compact_perturbation_ker_range hu.finite_ker hu.isClosed_range hh').1
    have hc := (FredholmBanach.compact_perturbation_coker
      ((FredholmBanach.isFredholm_iff_finiteDimensional u).1 hu).2 hh').1
    exact (FredholmBanach.isFredholm_iff_finiteDimensional (u + h')).2 ⟨hk, hc⟩
  -- the path `t ↦ u + t • h`
  let γ : ℝ → E →L[𝕜] F := fun t => u + ((t : 𝕜) • h)
  have hγc : Continuous γ :=
    continuous_const.add (Continuous.smul (f := fun t : ℝ => (t : 𝕜)) (g := fun _ => h)
      RCLike.continuous_ofReal continuous_const)
  have hγF : ∀ t : ℝ, (γ t).IsFredholm := fun t =>
    hF ((t : 𝕜) • h) (hh.smul (t : 𝕜))
  have hlc : IsLocallyConstant (fun t => FredholmBanach.index (γ t)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    exact (hγc.tendsto t).eventually
      ((FredholmBanach.isOpen_isFredholm_index_locallyConstant (𝕜 := 𝕜)).2 _ (hγF t))
  have h1 : γ 1 = u + h := by simp [γ]
  have h0 : γ 0 = u := by simp [γ]
  refine ⟨hF h hh, ?_⟩
  have := hlc.apply_eq_of_preconnectedSpace 1 0
  simpa [h1, h0] using this
