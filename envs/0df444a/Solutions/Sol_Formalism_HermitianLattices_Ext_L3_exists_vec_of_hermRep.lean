-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_vec_of_hermRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:21.49587+00:00
-- url     : https://prove2.me/submissions/5ee8f7d3-ecaa-486d-a1d2-2d6d48895ff6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finrank_perpSpace
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
private theorem star_sesq_eq_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (a b : V) :
    star (h a b) = h b a := by
  first | exact hs a b | exact hs.eq a b
end Formalism.HermitianLattices.Ext.L3
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hH : HermRepUnram) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) (hV : 2 ≤ finrank K V)
    (n : K) (hn : star n = n) (hpos : TotPos n) : ∃ x : V, h x x = n := by
  have hne : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hx φ
    rw [h0, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hfr := finrank_perpSpace (h := h) (hne x hx)
  obtain ⟨y', hy'⟩ : ∃ y : ↥(perpSpace h x), y ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hy0 : y'.1 ≠ 0 := fun h0 => hy' (Subtype.ext h0)
  have hxy : h x y'.1 = 0 := LinearMap.mem_ker.mp y'.2
  have hyx : h y'.1 x = 0 := by rw [← star_sesq_eq_swap_of_isSymm hs, hxy, star_zero]
  obtain ⟨s, t, hst⟩ := hH K hK (h x x) (h y'.1 y'.1) n (star_sesq_eq_swap_of_isSymm hs x x) (star_sesq_eq_swap_of_isSymm hs _ _) hn
    (fun φ => hd x hx φ) (fun φ => hd _ hy0 φ) hpos
  refine ⟨star s • x + star t • y'.1, ?_⟩
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    hxy, hyx, starRingEnd_apply, star_star]
  linear_combination hst
end Formalism.HermitianLattices.Ext.L3
