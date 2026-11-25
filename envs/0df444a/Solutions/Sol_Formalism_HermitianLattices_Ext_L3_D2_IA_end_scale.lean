-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.IA.end_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:39.204537+00:00
-- url     : https://prove2.me/submissions/67836219-a0ca-448e-9fa4-057f46e5c393

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_IA_unif_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_anti
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_ne_zero


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2 Formalism.HermitianLattices.Ext.L3.D2.IA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2.IA
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r r' : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (Y : V →ₗ[K] V) {n m : ℕ} (hnm : n + r + r' ≤ m)
    (hY : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ m • locF 𝔭 A₀) :
    ∀ x ∈ locF 𝔭 B₀, Y x ∈ extP K 𝔭 ^ n • locF 𝔭 B₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  intro x hx
  have hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀ :=
    hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have h1 := smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')
  obtain ⟨a, ha, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1
  have ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩
  rw [map_smul] at e
  apply smul_right_injective V (pow_ne_zero r' h0)
  show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _
  rw [e, smul_smul, smul_smul]
  congr 1
  ring
end Formalism.HermitianLattices.Ext.L3.D2.IA
