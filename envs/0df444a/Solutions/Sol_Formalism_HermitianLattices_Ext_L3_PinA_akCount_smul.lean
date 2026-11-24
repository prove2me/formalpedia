-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinA.akCount_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:19:34.042306+00:00
-- url     : https://prove2.me/submissions/043cc328-6291-4ffa-8b09-64756038d448

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealSmulLeIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_akM_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_akCount_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_exists_local_data


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.PinA
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    akCount (algebraMap F K (c : F) • h) L 𝔭 k =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V ^ 2) * akCount h L 𝔭 (k - vF 𝔭 c) := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, -⟩ := localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk,
    Fintype.card_fin]
end Formalism.HermitianLattices.Ext.L3.PinA
