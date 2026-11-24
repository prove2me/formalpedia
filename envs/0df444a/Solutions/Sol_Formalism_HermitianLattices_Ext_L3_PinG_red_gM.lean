-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinG.red_gM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:53.63135+00:00
-- url     : https://prove2.me/submissions/82b8cd2d-7efc-4e63-a08c-089f900c5f8f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_smul_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_bM
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_bO_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinG
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
omit [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.PinG
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b)))
    (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (gM hg w) = gMat b h𝔭 k hg *ᵥ red b h𝔭 k w := by
  have key : (red b h𝔭 k ∘ₗ gM hg) ∘ₗ Submodule.inclusion (le_locF 𝔭 (spanO b)) =
      (((gMat b h𝔭 k hg).mulVecLin.restrictScalars (𝓞 K)) ∘ₗ red b h𝔭 k) ∘ₗ
        Submodule.inclusion (le_locF 𝔭 (spanO b)) := by
    apply (bO b).ext
    intro j
    have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) (bO b j) = bM b 𝔭 j := by
      apply Subtype.ext
      exact bO_apply b j
    simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply]
    rw [red_bM, mulVec_single_one]
    rfl
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  have h1 := LinearMap.congr_fun key ⟨_, hcw⟩
  have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) ⟨_, hcw⟩ = ι c • w := rfl
  simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply] at h1
  rw [map_smul, red_smul_one b h𝔭 k hc, red_smul_one b h𝔭 k hc] at h1
  exact h1
end Formalism.HermitianLattices.Ext.L3.PinG
