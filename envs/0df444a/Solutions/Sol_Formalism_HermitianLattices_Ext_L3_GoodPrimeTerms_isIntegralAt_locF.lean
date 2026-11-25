-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms.isIntegralAt_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:37:26.233488+00:00
-- url     : https://prove2.me/submissions/79fbdb4e-8710-4e1d-9f98-557895b57fcd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFibGEqProd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_locF_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization
namespace Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    (hF : IsFixF K F) {C : Submodule (𝓞 K) W}
    (hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h₀ C) : IsIntegralAt 𝔭 h₀ (locF 𝔭 C) := by
  intro x hx y hy
  obtain ⟨s, hs, hx⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hx
  obtain ⟨t, ht, hy⟩ := (LocF.mem_locF_iff h𝔭 _ _).mp hy
  refine (LocF.mem_locF_iff h𝔭 _ _).mpr ⟨s * t, fun e => (h𝔭.mem_or_mem e).elim hs ht, ?_⟩
  have h1 := hCi _ hx _ hy
  have e : conjO K (algebraMap (𝓞 F) (𝓞 K) s) = algebraMap (𝓞 F) (𝓞 K) s :=
    (conjO_eq_iff_mem_range hF _).mpr ⟨s, rfl⟩
  have h2 : h₀ (algebraMap (𝓞 F) (𝓞 K) s • x) (algebraMap (𝓞 F) (𝓞 K) t • y) =
      (conjO K (algebraMap (𝓞 F) (𝓞 K) s) * algebraMap (𝓞 F) (𝓞 K) t) • h₀ x y := by
    have e' : algebraMap (𝓞 K) K (conjO K (algebraMap (𝓞 F) (𝓞 K) s)) =
      starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) s)) := rfl
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s) x,
      ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, map_smul, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Algebra.smul_def, map_mul, e']
    ring
  rw [h2, e, ← map_mul] at h1
  exact h1
end Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
