-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.akCount_eq_mul_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:43.669933+00:00
-- url     : https://prove2.me/submissions/48700d95-01fa-4bfe-a755-91d16fedefcc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_akCount_basis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_redCount_basis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_isUnit_det_of_form
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_conjTranspose_eq_of_symm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_card_cell
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
    (h𝔭 : 𝔭.IsMaximal) {c j : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 c) (hcj : c ≤ j) (hj : 1 ≤ j) :
    akCount h (locF 𝔭 (spanO b)) 𝔭 (j + c) =
      redCount h (locF 𝔭 (spanO b)) 𝔭 j * sigmaCount h (locF 𝔭 (spanO b)) 𝔭 c := by
  rw [akCount_basis h b hH h𝔭, redCount_basis hK hs hd b hH h𝔭 he hj, sigmaCount_basis h b hH h𝔭]
  exact card_cell h𝔭 (conjTranspose_eq_of_symm hs b hH) hcj
    (isUnit_det_of_form hK hs hd b hH h𝔭 he (by omega))
end Formalism.HermitianLattices.Ext.L3.HU
