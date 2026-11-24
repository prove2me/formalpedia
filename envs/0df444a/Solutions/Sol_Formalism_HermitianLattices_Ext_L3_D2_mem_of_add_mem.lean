-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_of_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:21.917472+00:00
-- url     : https://prove2.me/submissions/c1149374-e84b-4ddd-953b-e2292b397af1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_pow_smul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_pow_mem_pK_zero
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_zero
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) (j : ℕ) {w : V}
    (hw : w + D w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) : w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  set p : K := algebraMap F K (π : F) with hp
  have key : ∀ w : V, w + D w ∈ locF 𝔭 A₀ → w ∈ locF 𝔭 A₀ := by
    intro w hw
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hA₀ h𝔭 hπ w
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      apply ih
      have h1 : D (p ^ (n + 1) • w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        rw [pow_one]; exact hD _ hn
      have h2 : p ^ (n + 1) • (w + D w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ :=
        (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨p ^ n • (w + D w),
          smul_mem_locF h𝔭 A₀ (unif_pow_mem_pK_zero hπ n) hw, by rw [smul_smul, pow_one, pow_succ']⟩
      have h3 : p ^ (n + 1) • w ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        have := sub_mem h2 h1
        rwa [map_smul, smul_add, add_sub_cancel_right] at this
      obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h3
      have : p ^ n • w = y := by
        apply smul_right_injective V hπ0
        show p • p ^ n • w = p • y
        rw [smul_smul, ← pow_succ', e, pow_one]
      rwa [this]
  obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hw
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨(p ^ j)⁻¹ • w, key _ ?_, ?_⟩
  · rw [map_smul, ← smul_add, e, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hπ0), one_smul]
    exact hy
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero j hπ0), one_smul]
end Formalism.HermitianLattices.Ext.L3.D2
