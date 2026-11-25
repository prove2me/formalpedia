-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.map_maxGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:08.376202+00:00
-- url     : https://prove2.me/submissions/129246da-7705-4055-8633-88af5e6e9471

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (φ : M ≃ₗ[ℂ] M') (T : Module.End ℂ M) (T' : Module.End ℂ M') (hφ : ∀ x, φ (T x) = T' (φ x)) (μ : ℂ) :
    (T.maxGenEigenspace μ).map (φ : M →ₗ[ℂ] M') = T'.maxGenEigenspace μ := by
  have key : ∀ (k : ℕ) (x : M), φ (((T - μ • (1 : Module.End ℂ M)) ^ k) x) =
      ((T' - μ • (1 : Module.End ℂ M')) ^ k) (φ x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hφ]
  ext y
  rw [Submodule.mem_map_equiv, Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := key k (φ.symm y)
    rw [hk, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply φ.injective
    rw [key, LinearEquiv.apply_symm_apply, hk, map_zero]
end CompanionTheory.RgExh.Hk
