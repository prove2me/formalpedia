-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.near_region_total_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:59.787651+00:00
-- url     : https://prove2.me/submissions/bcfa2a87-94f4-4889-bfa5-758c20a2f349

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_log_ydat
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ydat_facts
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : NearTotalAbs := by
  intro c hc
  refine ⟨c / 4, c / 2, by positivity, by positivity, ?_⟩
  intro C Cg hC hCg
  have hK0 : 0 ≤ Real.log (C * (Cg + 4)) := Real.log_nonneg (by nlinarith)
  refine ⟨
    ⌈Real.exp (4 * (5 + Real.log (C * (Cg + 4))) / c)⌉₊, ?_⟩
  intro n q J a f rd g b hn hq ha haJ hJq hf hlf hb hg hgb hrd hllrd hllb
  have hn1 : Real.exp (4 * (5 + Real.log (C * (Cg + 4))) / c) ≤ n := Nat.ceil_le.mp hn
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn1
  have hlog : 4 * (5 + Real.log (C * (Cg + 4))) / c ≤ Real.log n :=
    (Real.le_log_iff_exp_le hn0).mpr hn1
  have hlog' : 4 * (5 + Real.log (C * (Cg + 4))) ≤ c * Real.log n := by
    rw [div_le_iff₀ hc] at hlog; linarith
  have hnN : 1 ≤ n := by
    have : 0 < n := by exact_mod_cast hn0
    omega
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hnN
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast ha.trans haJ
  have hLn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hY := log_ydat hnN hf hrd hg hb
  have hKe : C * (Cg + 4) = Real.exp (Real.log (C * (Cg + 4))) := (Real.exp_log (by positivity)).symm
  generalize Real.log (C * (Cg + 4)) = K at *
  have hx0 : 0 ≤ c / 4 * ((n:ℝ) * f * Real.log n) := by positivity
  have hlrd : Real.log rd ≤ Real.exp n := by
    rcases (Real.log_nonneg hrd).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact (Real.log_le_iff_le_exp h0).mp hllrd
  have hlb0 : 0 < Real.log b := Real.log_pos (by linarith)
  have hlb : Real.log b ≤ Real.exp (c / 4 * ((n:ℝ) * f * Real.log n)) :=
    (Real.log_le_iff_le_exp hlb0).mp (by
      have e : c / 4 * ((n:ℝ) * f * Real.log n) = c / 4 * n * f * Real.log n := by ring
      rw [e]; exact hllb)
  have hlg : Real.log g ≤ Cg * Real.log b := by
    have := Real.log_le_log (by linarith) hgb
    rwa [Real.log_rpow (by linarith)] at this
  have hne : (n:ℝ) ≤ Real.exp n := by have := Real.add_one_le_exp (n:ℝ); linarith
  have hsn : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hlnn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hfe : (f:ℝ) ≤ Real.exp n := by
    rw [← Real.log_le_iff_le_exp (by linarith)]; linarith
  have hq2 : (q:ℝ) ^ 2 ≤ Real.exp n := by
    have : (q:ℝ) ^ 2 ≤ n := by exact_mod_cast hq
    linarith
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  generalize hxdef : c / 4 * ((n:ℝ) * f * Real.log n) = x4 at *
  have hE1 : Real.exp n ≤ Real.exp (n + x4) := Real.exp_le_exp.mpr (by linarith)
  have hE2 : Real.exp x4 ≤ Real.exp (n + x4) := Real.exp_le_exp.mpr (by linarith)
  have hLY : Real.log (Ydat n f rd g b) ≤ (Cg + 4) * Real.exp (n + x4) := by
    rw [hY]
    have h1 : Cg * Real.log b ≤ Cg * Real.exp (n + x4) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    linarith
  have hLY0 : 0 ≤ Real.log (Ydat n f rd g b) :=
    Real.log_nonneg (by have := (ydat_facts hnN hf hrd hg hb).1; linarith)
  generalize Real.log (Ydat n f rd g b) = LY at *
  have hbr : C * f * (q:ℝ) ^ 2 * LY ≤ Real.exp (K + 3 * n + x4) := by
    calc C * f * (q:ℝ) ^ 2 * LY ≤ C * Real.exp n * Real.exp n * ((Cg + 4) * Real.exp (n + x4)) := by
          gcongr
      _ = (C * (Cg + 4)) * (Real.exp n * Real.exp n * Real.exp (n + x4)) := by ring
      _ = _ := by
          rw [hKe, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hM0 : 0 ≤ K + 3 * n + x4 := by positivity
  have hpow : (C * f * (q:ℝ) ^ 2 * LY) ^ a ≤ Real.exp ((J:ℝ) * (K + 3 * n + x4)) := by
    calc (C * f * (q:ℝ) ^ 2 * LY) ^ a ≤ (Real.exp (K + 3 * n + x4)) ^ a := by
          apply pow_le_pow_left₀ (by positivity) hbr
      _ ≤ (Real.exp (K + 3 * n + x4)) ^ J := pow_le_pow_right₀ (Real.one_le_exp hM0) haJ
      _ = _ := (Real.exp_nat_mul _ _).symm
  have h2q : (2:ℝ) ^ q * 2 ≤ Real.exp ((q:ℝ) + 1) := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
    calc (2:ℝ) ^ q * 2 = 2 ^ (q + 1) := by ring
      _ ≤ (Real.exp 1) ^ (q + 1) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (2:ℝ) ^ q * (2 * Real.exp (-(c * J * n * f * Real.log n))) * (C * f * (q:ℝ) ^ 2 * LY) ^ a
      = ((2:ℝ) ^ q * 2) * Real.exp (-(c * J * n * f * Real.log n)) * (C * f * (q:ℝ) ^ 2 * LY) ^ a := by
        ring
    _ ≤ Real.exp ((q:ℝ) + 1) * Real.exp (-(c * J * n * f * Real.log n))
          * Real.exp ((J:ℝ) * (K + 3 * n + x4)) := by gcongr
    _ = Real.exp ((q:ℝ) + 1 + -(c * J * n * f * Real.log n) + (J:ℝ) * (K + 3 * n + x4)) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have e1 : c * J * n * f * Real.log n = J * (4 * x4) := by rw [← hxdef]; ring
        have e2 : c / 2 * n * f * Real.log n = 2 * x4 := by rw [← hxdef]; ring
        rw [e1, e2]
        have h5 : (5 + K) * n ≤ x4 := by
          rw [← hxdef]
          calc (5 + K) * n = (4 * (5 + K)) / 4 * (n * 1) := by ring
            _ ≤ (c * Real.log n) / 4 * (n * f) := by gcongr
            _ = _ := by ring
        have h6 : (q:ℝ) + 1 ≤ J * (n + 1) := by
          have : 1 * ((n:ℝ) + 1) ≤ J * (n + 1) := by gcongr
          linarith
        have h7 : (n:ℝ) + 1 + K + 3 * n ≤ x4 := by
          have : K * 1 ≤ K * n := by gcongr
          linarith
        have h8 : (J:ℝ) * (n + 1 + K + 3 * n) ≤ J * x4 := by gcongr
        have h9 : 1 * x4 ≤ J * x4 := by gcongr
        linarith
end Formalism.HermitianLatticeCounting.P
