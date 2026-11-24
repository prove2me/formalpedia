-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_glSub_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:50:47.739044+00:00
-- url     : https://prove2.me/submissions/0396bbbc-0726-4fe5-a866-dd570710bab9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsEquivOfMemEndL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_equiv_of_mem_endL
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {X : V ≃ₗ[K] V}
    (hX : ∀ x ∈ locF 𝔭 A₀, X x - x ∈ extP K 𝔭 • locF 𝔭 A₀) : X ∈ glSub (locF 𝔭 A₀) := by
  obtain ⟨Y, hY, hY'⟩ := exists_equiv_of_mem_endL hA₀ h𝔭
    (D := (X : V →ₗ[K] V) - LinearMap.id) (fun x hx => hX x hx)
  have : X = Y := by
    ext x
    rw [hY]
    simp
  rwa [this]
end Formalism.HermitianLattices.Ext.L3.D2
