-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallSum.exists_mem_boxSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:30.90422+00:00
-- url     : https://prove2.me/submissions/b41e4d03-f02a-43f3-8558-c2edd431b773

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IntegralOfMemGenus
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_exists_int_of_star_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallSum
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallSum
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} {x : V}
    (hx : x ∈ M) (hx0 : x ≠ 0) (hxT : ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T) :
    ∃ n ∈ boxSet K F T, h x x = algebraMap F K (n : F) := by
  have hsym : star (h x x) = h x x := by
    rw [← starRingEnd_apply]
    exact hs.eq x x
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hMi x hx x hx)
  have hy' : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y := by rw [hy]; exact hsym
  obtain ⟨n, hn⟩ := QuadraticExtensionConjugation.exists_int_of_star_eq hF y hy'
  have hkey : h x x = algebraMap F K (n : F) := by
    rw [← hy, ← hn]
    rfl
  refine ⟨n, fun φ => ?_, hkey⟩
  rw [← hkey]
  exact ⟨hd x hx0 φ, hxT φ⟩
end Formalism.HermitianLattices.Ext.L3.BallSum
