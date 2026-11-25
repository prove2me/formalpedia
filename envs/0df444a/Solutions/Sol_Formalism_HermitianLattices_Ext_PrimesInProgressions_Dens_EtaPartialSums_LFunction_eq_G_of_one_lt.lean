-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums.LFunction_eq_G_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:57.179821+00:00
-- url     : https://prove2.me/submissions/b092b190-beee-4d5b-822a-df082709b292

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLs
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_Ap_eps_le
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_tendsto_G
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_sum_Icc_eq_sum_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_partial_tendsto_G


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
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) : ZMod.LFunction Φe s = G eps s := by
  rw [ZMod.LFunction_eq_LSeries Φe hs]
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, eps n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (LSeries (fun n => Φe n) s)) := by
    have hsum := (ZMod.LSeriesSummable_of_one_lt_re Φe hs).hasSum.tendsto_sum_nat
    have h2 := hsum.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun M => ?_)
    simp only [Function.comp_apply]
    rw [← Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range _ (LSeries.term_zero _ _)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
    rfl
  exact tendsto_nhds_unique h1 (partial_tendsto_G eps norm_Ap_eps_le (by linarith))
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
