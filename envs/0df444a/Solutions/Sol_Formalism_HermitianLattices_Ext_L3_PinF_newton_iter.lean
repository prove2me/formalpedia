-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinF.newton_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:16.309875+00:00
-- url     : https://prove2.me/submissions/e6ddf2aa-2dd4-4bcc-b1a0-9417cc0c419d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsExactLift
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinF_newton
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_zero
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinF
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.PinF
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) {y : V}
    (hy : y ∈ L) {a : 𝓞 F} (ha : h y y = algebraMap (𝓞 K) K (ι a)) (ha1 : a - 1 ∈ 𝔭 ^ k) (j : ℕ) :
    ∃ y' ∈ L, ∃ a' : 𝓞 F, h y' y' = algebraMap (𝓞 K) K (ι a') ∧ a' - 1 ∈ 𝔭 ^ (k + j) ∧
      y' - y ∈ (extP K 𝔭 ^ k • L : Submodule (𝓞 K) V) := by
  induction j with
  | zero => exact ⟨y, hy, a, ha, by simpa using ha1, by simp⟩
  | succ j ih =>
    obtain ⟨y1, hy1, a1, hh1, h1, hd1⟩ := ih
    obtain ⟨y2, hy2, a2, hh2, h2, hd2⟩ := newton hK hF h𝔭 (by omega : 1 ≤ k + j) hy1 hh1 h1
    refine ⟨y2, hy2, a2, hh2, by simpa only [add_assoc] using h2, ?_⟩
    have : y2 - y = (y2 - y1) + (y1 - y) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hd2) hd1
end Formalism.HermitianLattices.Ext.L3.PinF
