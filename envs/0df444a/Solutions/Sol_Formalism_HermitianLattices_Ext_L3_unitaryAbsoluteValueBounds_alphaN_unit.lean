-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.alphaN_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:14:10.999281+00:00
-- url     : https://prove2.me/submissions/0ef9f990-739e-4eac-80eb-d6c2a12151dd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_nkCount_eq_cnt
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_one_lt_q


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    alphaN h L 𝔭 n =
      1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by have := one_lt_q h𝔭; linarith
  rw [alphaN]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [nkCount_eq_cnt hK hF hs hd hL hLi h𝔭 hv hk n, cnt_unit hK hF h𝔭 hm hk hn,
    show k * (2 * finrank K V - 1) = (2 * finrank K V - 1) * k from mul_comm _ _,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
