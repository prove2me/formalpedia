-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.sigmaCount_succ_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:55:21.887652+00:00
-- url     : https://prove2.me/submissions/8f3fc783-3ed2-4f17-bac7-bd66c9adfe7d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_conjTranspose_eq_of_symm
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_exists_E__cec9a940fda7
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_card_sigma_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_sigmaCount_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {e j : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hj : e ≤ j) :
    sigmaCount h (locF 𝔭 (spanO b)) 𝔭 (j + 1) =
      Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) * sigmaCount h (locF 𝔭 (spanO b)) 𝔭 j := by
  obtain ⟨E₀, d, hd1, hHE⟩ := exists_E₀ hFF.out hd b hH h𝔭 he
  rw [sigmaCount_basis h b hH h𝔭, sigmaCount_basis h b hH h𝔭]
  exact card_sigma_succ hK h𝔭 (conjTranspose_eq_of_symm hs b hH) hd1 hHE hj
end Formalism.HermitianLattices.Ext.L3.HU
