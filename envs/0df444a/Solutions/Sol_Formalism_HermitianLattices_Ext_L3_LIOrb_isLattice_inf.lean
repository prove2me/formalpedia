-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.isLattice_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:41:10.210617+00:00
-- url     : https://prove2.me/submissions/f939de90-13d7-4d57-ae72-8a06acc1fa63

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_zsmul_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) : Submodule.IsLattice K (M₁ ⊓ M₂) where
  fg := by
    have : Module.Finite (𝓞 K) ↥M₁ := Module.Finite.iff_fg.2 hM₁.fg
    have : IsNoetherian (𝓞 K) ↥M₁ := inferInstance
    have : IsNoetherian (𝓞 K) ↥(M₁ ⊓ M₂) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM₁ hM₂
    rw [eq_top_iff, ← hM₁.span_eq_top, Submodule.span_le]
    intro x hx
    have h1 : n • x ∈ Submodule.span K ((M₁ ⊓ M₂ : Submodule (𝓞 K) V) : Set V) :=
      Submodule.subset_span ⟨zsmul_mem hx n, hnx x hx⟩
    have h2 := Submodule.smul_mem _ ((n : K)⁻¹) h1
    rwa [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
      one_smul] at h2
end Formalism.HermitianLattices.Ext.L3.LIOrb
