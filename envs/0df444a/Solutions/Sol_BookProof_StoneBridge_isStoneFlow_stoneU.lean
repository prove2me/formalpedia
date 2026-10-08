-- Prove2me | solution 1 for BookProof.StoneBridge.isStoneFlow_stoneU
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:55:56.824018+00:00
-- url     : https://prove2.me/submissions/f025b892-31a7-48cc-a1e7-488e47e8fccf

import Mathlib
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterYangMillsHermite

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace
open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.StoneBridge

namespace P2M09674018

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The flow commutes with the operator on the domain. -/
theorem op_stoneU (T : UnboundedSelfAdjoint F) (t : ℝ) (x : F) (hx : x ∈ T.domain)
    (h : T.stoneU t x ∈ T.domain) :
    T.op ⟨T.stoneU t x, h⟩ = T.stoneU t (T.op ⟨x, hx⟩) := by
  set xd : T.domain := ⟨x, hx⟩ with hxd
  have hres : ((T.res 1 (T.shift 1 xd) : T.domain) : F) = x := by
    rw [T.res_shift one_ne_zero]
  have hU : T.stoneU t x = T.resCLM 1 (T.stoneU t (T.shift 1 xd)) := by
    rw [← T.stoneU_commute_resCLM]
    congr 1
    exact hres.symm
  have hel : (⟨T.stoneU t x, h⟩ : T.domain) = T.res 1 (T.stoneU t (T.shift 1 xd)) := by
    apply Subtype.ext
    exact hU
  rw [hel, T.op_res one_ne_zero, ← T.resCLM_apply, ← hU, T.shift_apply, map_sub, map_smul]
  have hxx : ((xd : T.domain) : F) = x := rfl
  rw [hxx]
  abel

/-- Differentiability of the flow at `0` on the domain. -/
theorem stoneU_sub_isLittleO (T : UnboundedSelfAdjoint F) (x : T.domain) :
    (fun h : ℝ => T.stoneU h (x : F) - (x : F) - h • ((-Complex.I) • T.op x))
      =o[𝓝 0] (fun h : ℝ => h) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (T.yosida_tendsto x) (c / 3) (by positivity)
  set k : ℝ := (N : ℝ) + 1 with hkdef
  have hk : ‖T.yosida k (x : F) - T.op x‖ ≤ c / 3 := by
    have := hN N le_rfl
    rw [dist_eq_norm] at this
    exact this.le
  have hd := T.hasDerivAt_approxU_apply k 0 (x : F)
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hd
  have hd' := (Asymptotics.isLittleO_iff.mp hd) (show (0 : ℝ) < c / 3 by positivity)
  filter_upwards [hd'] with h hh
  simp only [zero_add, T.approxU_zero, one_mul, ContinuousLinearMap.one_apply] at hh
  have hgen : T.yosidaGen k (x : F) = (-Complex.I) • T.yosida k (x : F) := by
    simp [UnboundedSelfAdjoint.yosidaGen]
  rw [hgen] at hh
  have h1 : ‖T.stoneU h (x : F) - T.approxU k h (x : F)‖ ≤ |h| * (c / 3) := by
    calc ‖T.stoneU h (x : F) - T.approxU k h (x : F)‖
        ≤ |h| * ‖T.op x - T.yosida k (x : F)‖ := T.norm_stoneU_sub_approxU_le k h x
      _ ≤ |h| * (c / 3) := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_left hk (abs_nonneg h)
  have h3 : ‖h • ((-Complex.I) • (T.yosida k (x : F) - T.op x))‖ ≤ |h| * (c / 3) := by
    rw [norm_smul, norm_smul, norm_neg, Complex.norm_I, one_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hk (abs_nonneg h)
  have hsplit : T.stoneU h (x : F) - (x : F) - h • ((-Complex.I) • T.op x)
      = (T.stoneU h (x : F) - T.approxU k h (x : F))
        + (T.approxU k h (x : F) - (x : F) - h • ((-Complex.I) • T.yosida k (x : F)))
        + h • ((-Complex.I) • (T.yosida k (x : F) - T.op x)) := by
    simp only [smul_sub]
    abel
  rw [hsplit, Real.norm_eq_abs]
  have h2 : ‖T.approxU k h (x : F) - (x : F) - h • ((-Complex.I) • T.yosida k (x : F))‖
      ≤ c / 3 * |h| := by
    simpa [Real.norm_eq_abs] using hh
  calc _ ≤ ‖(T.stoneU h (x : F) - T.approxU k h (x : F))
        + (T.approxU k h (x : F) - (x : F) - h • ((-Complex.I) • T.yosida k (x : F)))‖
        + ‖h • ((-Complex.I) • (T.yosida k (x : F) - T.op x))‖ := norm_add_le _ _
    _ ≤ ‖T.stoneU h (x : F) - T.approxU k h (x : F)‖
        + ‖T.approxU k h (x : F) - (x : F) - h • ((-Complex.I) • T.yosida k (x : F))‖
        + ‖h • ((-Complex.I) • (T.yosida k (x : F) - T.op x))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ |h| * (c / 3) + c / 3 * |h| + |h| * (c / 3) := by gcongr
    _ = c * |h| := by ring

end P2M09674018

open BookProof.ChapterStoneResolvent BookProof.StoneBridge in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : UnboundedSelfAdjoint F) : IsStoneFlow T T.stoneU := by
  refine ⟨T.stoneU_zero, T.stoneU_add, T.norm_stoneU_apply, ?_⟩
  intro x hx t
  refine ⟨T.stoneU_mem_domain t ⟨x, hx⟩, ?_⟩
  rw [P2M09674018.op_stoneU T t x hx]
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have key := P2M09674018.stoneU_sub_isLittleO T ⟨x, hx⟩
  have hfun : (fun h : ℝ => T.stoneU (t + h) x - T.stoneU t x
      - h • ((-Complex.I) • T.stoneU t (T.op ⟨x, hx⟩)))
      = fun h : ℝ => T.stoneU t (T.stoneU h x - x - h • ((-Complex.I) • T.op ⟨x, hx⟩)) := by
    funext h
    rw [T.stoneU_add t h, map_sub, map_sub, ContinuousLinearMap.map_smul_of_tower, map_smul]
    rfl
  rw [hfun, ← Asymptotics.isLittleO_norm_left]
  simp only [T.norm_stoneU_apply]
  exact Asymptotics.isLittleO_norm_left.mpr key
