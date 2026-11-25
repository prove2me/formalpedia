-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.alphaN_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:17:16.440953+00:00
-- url     : https://prove2.me/submissions/0b609354-7f7e-4de6-9dc5-dc0c4774ad38

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_alphaN_eq_stage
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_two_le_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_nkCount_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_two_le_absNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 → 0 ≤ alphaN h L 𝔭 n ∧ alphaN h L 𝔭 n ≤ C := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := alphaN_eq_stage hK hF hs hd hL hLi h𝔭 hn
  rw [hk]
  exact ⟨by positivity, (div_le_iff₀ (by positivity)).mpr (hC k n)⟩
end Formalism.HermitianLattices.Ext.L3.A5
