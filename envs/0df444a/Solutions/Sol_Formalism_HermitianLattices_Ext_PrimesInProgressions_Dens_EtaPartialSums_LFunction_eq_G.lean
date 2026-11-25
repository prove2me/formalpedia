-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.LFunction_eq_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:00.093542+00:00
-- url     : https://prove2.me/submissions/94707c69-8606-4751-bbc8-279e759c6085

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums__e_sum_3ff34a819f1f
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_Ap_eps_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_LFunction_eq_G_of_one_lt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_G_differentiableOn
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_LFunction_eq_G_of_one_lt
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_G_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) : ZMod.LFunction Φe s = G eps s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hf : AnalyticOnNhd ℂ (ZMod.LFunction Φe) {s : ℂ | 0 < s.re} :=
    (ZMod.differentiable_LFunction_of_sum_zero Φe_sum).differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (G eps) {s : ℂ | 0 < s.re} :=
    (G_differentiableOn eps norm_Ap_eps_le).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : ZMod.LFunction Φe =ᶠ[𝓝 (2 : ℂ)] G eps := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact LFunction_eq_G_of_one_lt hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn h2 hev hs
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
