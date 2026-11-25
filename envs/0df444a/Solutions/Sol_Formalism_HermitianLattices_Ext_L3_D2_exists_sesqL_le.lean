-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.exists_sesqL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:00:02.080159+00:00
-- url     : https://prove2.me/submissions/d4d1926f-6d63-4895-b27b-af73a4f09a2b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_smul_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_pK_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ∀ d : ℕ, sesqL (locF 𝔭 A₀) 𝔭 (d + r) ≤ sesqL (locF 𝔭 B₀) 𝔭 d := by
  obtain ⟨r2, h2⟩ := exists_smul_le hB₀ hA₀ h𝔭
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  refine ⟨r2 + r2, fun d s hs x hx y hy => ?_⟩
  have hx' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have hy' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)
  obtain ⟨c, hc, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (hs _ hx' _ hy')
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨c, hc, ?_⟩
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
    star_pow, MeanB.star_algebraMap hF] at e
  apply mul_left_cancel₀ (pow_ne_zero (r2 + r2) hπ0)
  rw [pow_add, pow_add] at *
  linear_combination e
end Formalism.HermitianLattices.Ext.L3.D2
