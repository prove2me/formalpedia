-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.star_mem_extP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:49.323857+00:00
-- url     : https://prove2.me/submissions/e70a1c7a-7375-46e1-9fdb-3ff036529d06

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_algebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_exists_star_int
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    ∃ z' ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z' = star (algebraMap (𝓞 K) K z) := by
  rw [extP, ← Ideal.map_pow, Ideal.map] at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨_, Ideal.subset_span ⟨t, ht, rfl⟩, by rw [algebraMap_comp, star_algebraMap hF]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, map_add, star_add, ex, ey]⟩
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := exists_star_int a
    exact ⟨a' * x', Ideal.mul_mem_left _ _ hx', by
      rw [smul_eq_mul, map_mul, map_mul, star_mul', ex, ea]⟩
end Formalism.HermitianLattices.Ext.L3.MeanB
