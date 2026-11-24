-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:21.031076+00:00
-- url     : https://prove2.me/submissions/2994ab00-d927-4a7b-b453-80f2d589b38b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_akCount_free
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_akCount_locF


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (b : Basis κ K V) (hb : locF 𝔭 (spanO b) = locF 𝔭 L) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) (k : ℕ) :
    akCount h L 𝔭 k = Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} := by
  have hF : IsFixF K F := Fact.out
  rw [← akCount_free h b hH h𝔭, ← akCount_locF hF h L 𝔭 h𝔭, ← hb, akCount_locF hF h _ 𝔭 h𝔭]
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
