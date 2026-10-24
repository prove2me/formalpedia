-- Prove2me | solution 1 for BilinearMapExtension.Complemented.linear_extension_of_bilinear_extension
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:48.781295+00:00
-- url     : https://prove2.me/submissions/fc0cef5f-f04d-4f37-8d6a-e0f45e01fcad

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

open BilinearMapExtension.Complemented

/-- Bilinear extension yields linear extension by taking a nonzero scalar section. -/
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y)
    (h : ∀ φ : M →L[𝕜] N →L[𝕜] Z, ∃ φh : X →L[𝕜] Y →L[𝕜] Z,
      IsBilinExtension M N φ φh) :
    (N ≠ ⊥ → ∀ T : M →L[𝕜] Z, ∃ Th : X →L[𝕜] Z, ∀ u : M, Th u = T u) ∧
    (M ≠ ⊥ → ∀ S : N →L[𝕜] Z, ∃ Sh : Y →L[𝕜] Z, ∀ v : N, Sh v = S v) := by
  constructor
  · intro hN T
    let : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
    obtain ⟨v, hv⟩ := exists_ne (0 : N)
    obtain ⟨g, _hg, hgv⟩ := exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)
    have hg0 : g v ≠ 0 := by
      rw [hgv]
      exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
    let φ : M →L[𝕜] N →L[𝕜] Z := (ContinuousLinearMap.smulRightL 𝕜 N Z g).comp T
    obtain ⟨φh, hφ⟩ := h φ
    refine ⟨(g v)⁻¹ • φh.flip v, ?_⟩
    intro u
    change (g v)⁻¹ • φh u v = T u
    rw [hφ u v]
    simp [φ, smul_smul, hg0]
  · intro hM S
    let : Nontrivial M := Submodule.nontrivial_iff_ne_bot.mpr hM
    obtain ⟨u, hu⟩ := exists_ne (0 : M)
    obtain ⟨g, _hg, hgu⟩ := exists_dual_vector 𝕜 u (norm_ne_zero_iff.mpr hu)
    have hg0 : g u ≠ 0 := by
      rw [hgu]
      exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
    let φ : M →L[𝕜] N →L[𝕜] Z := g.smulRight S
    obtain ⟨φh, hφ⟩ := h φ
    refine ⟨(g u)⁻¹ • φh u, ?_⟩
    intro v
    change (g u)⁻¹ • φh u v = S v
    rw [hφ u v]
    simp [φ, smul_smul, hg0]
