-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.sigmaCount_pos_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:28:41.427314+00:00
-- url     : https://prove2.me/submissions/46fc1937-19ce-4f1b-a76c-83c8f67724a1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCountPosBasis
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_sigmaCount_basis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution [Fact (IsFixF K F)] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (j : ℕ) : 0 < sigmaCount h (locF 𝔭 (spanO b)) 𝔭 j := by
  rw [sigmaCount_basis h b hH h𝔭]
  have := finite_quot (K := K) h𝔭 j
  have : Nonempty {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) // Hq H 𝔭 j * Y + Yᴴ * Hq H 𝔭 j = 0} :=
    ⟨⟨0, by simp⟩⟩
  exact Nat.card_pos
end Formalism.HermitianLattices.Ext.L3.HU
