-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:00:19.894172+00:00
-- url     : https://prove2.me/submissions/2f80e198-ae41-42fd-9a52-6855cf6000c7

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution {P : Par} {e K : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) :
    ∃ z u E X S sb v w8 : ℝ, Facts P e K z u E X S sb v w8 := by
  obtain ⟨hε, hε1, he, hK, ⟨n2x, n2n⟩, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE, Sc0, ScS, η0, ηS,
    ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, β0, βK, Co0, CoK, Y1, YX, s0, sx, bo0, bosb⟩ := hW
  have nx := n2x.trans n2n
  obtain ⟨x1, hC, hB, hA⟩ := hL
  have xpos : 0 < P.x := by linarith
  have e4 : P.x ^ (4 * P.ε) = (P.x ^ P.ε) ^ 4 := by
    rw [mul_comm, Real.rpow_mul xpos.le, Real.rpow_ofNat]
  have e2 : P.x ^ (2 * P.ε) = (P.x ^ P.ε) ^ 2 := by
    rw [mul_comm, Real.rpow_mul xpos.le, Real.rpow_ofNat]
  have eM : P.x ^ (4 * e + 4) = (P.x ^ e) ^ 4 * P.x ^ 4 := by
    rw [Real.rpow_add xpos, mul_comm 4 e, Real.rpow_mul xpos.le, Real.rpow_ofNat, Real.rpow_ofNat]
  rw [e4] at hC
  rw [e2] at Laz
  rw [eM] at hB hA
  rw [Real.exp_add] at hA
  have z1 : 1 ≤ P.x ^ P.ε := Real.one_le_rpow x1 hε.le
  have u1 : 1 ≤ P.x ^ (P.ε / 3) := Real.one_le_rpow x1 (by positivity)
  have E1 : 1 ≤ P.x ^ e := Real.one_le_rpow x1 he
  have z41 : 1 ≤ (P.x ^ P.ε) ^ 4 := one_le_pow₀ z1
  have hx : 100 ≤ P.x := by
    have h1 : 1 ≤ K * (P.x ^ P.ε) ^ 4 := one_le_mul_of_one_le_of_one_le hK z41
    linarith only [h1, hC]
  have hM1 : 1 ≤ (P.x ^ e) ^ 4 * P.x ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ E1) (one_le_pow₀ x1)
  have lx0 : 0 ≤ Real.log P.x := Real.log_nonneg x1
  have hlog : Real.log P.x * (4 * e + 4) ≤ P.x ^ (P.ε / 3) := by
    have h1 : P.x ^ (4 * e + 4) ≤ Real.exp (P.x ^ (P.ε / 3)) := by
      rw [eM]
      have h2 : (1 : ℝ) ≤ 100 * K := by linarith only [hK]
      exact (le_mul_of_one_le_left (by linarith only [hM1]) h2).trans hB
    rwa [Real.rpow_def_of_pos xpos, Real.exp_le_exp] at h1
  have uz : P.x ^ (P.ε / 3) ≤ P.x ^ P.ε := Real.rpow_le_rpow_of_exponent_le x1 (by linarith)
  have helx : 0 ≤ e * Real.log P.x := mul_nonneg he lx0
  have hlog' : 4 * (e * Real.log P.x) + 4 * Real.log P.x ≤ P.x ^ (P.ε / 3) := by
    have : Real.log P.x * (4 * e + 4) = 4 * (e * Real.log P.x) + 4 * Real.log P.x := by ring
    linarith only [this, hlog]
  have Xpos : 0 < Real.exp (P.x ^ (P.ε / 3)) := Real.exp_pos _
  have bpos : 0 < Real.exp (P.x ^ P.ε) := Real.exp_pos _
  have npos : 0 < P.n := lt_of_lt_of_le (by positivity) n2n
  refine ⟨P.x ^ P.ε, P.x ^ (P.ε / 3), P.x ^ e, Real.exp (P.x ^ (P.ε / 3)), Real.exp (P.x ^ (P.ε / 4)),
    Real.exp (P.x ^ P.ε / 2), Real.exp (P.x ^ P.ε) / Real.exp (P.x ^ (P.ε / 3)), P.x ^ (P.ε / 8), ?_⟩
  exact
  { hx := hx, he := he, hK := hK, z1 := z1, hz4 := hC, u1 := u1, uz := uz, E1 := E1, hXB := hB
    S1 := Real.one_le_exp (Real.rpow_nonneg xpos.le _)
    hsb := hA
    hb := by
      unfold Par.b bTx
      rw [← Real.exp_add, add_halves]
    ha := by simp only [Par.a, Par.b, aTx]
    hXp := by simp only [Par.Xp, XpTx]
    hvX := by unfold Par.b bTx; field_simp
    v0 := by positivity
    hbp := by unfold Par.bp bpTx aTx bTx XpTx; ring
    hwpp := by
      unfold Par.wpp wppTx bpTx aTx bTx XpTx
      field_simp
    hXpp := by
      unfold Par.Xpp XppTx wppTx bpTx aTx bTx XpTx
      field_simp
    lx0 := lx0
    lxz := by unfold Par.lx; linarith only [hlog', helx, lx0, uz]
    elx := by unfold Par.lx; linarith only [hlog', helx, lx0, uz]
    logX := Real.log_exp _
    loga := by
      unfold Par.a aTx bTx Par.lx
      rw [Real.log_mul xpos.ne' bpos.ne', Real.log_exp]
    nx := nx, n2x := n2x, n2n := n2n, nE := nE, kx := kx, kE := kE, N0 := N0, NE := NE, t0 := t0, tE := tE, px := px, pE := pE
    La0 := La0, Laz := Laz, r0 := r0, rE := rE, Sc0 := Sc0, ScS := ScS, η0 := η0, ηS := ηS, ρ0 := ρ0
    ρx := ρx, th0 := th0, thx := thx, x_sq_le_threshold := x_sq_le_threshold, dx := dx, C0 := C0, CK := CK, β0 := β0, βK := βK
    Co0 := Co0, CoK := CoK, Y1 := Y1, YX := YX, s0 := s0, sx := sx, bo0 := bo0, bosb := bosb
    hδ := by unfold Par.δ₁; rw [Real.rpow_neg xpos.le]
    w81 := Real.one_le_rpow x1 (by positivity)
    w8z := Real.rpow_le_rpow_of_exponent_le x1 (by linarith)
    hθ := by unfold Par.θ; rw [Real.rpow_neg xpos.le]
    Joz := (Nat.floor_le (Real.rpow_nonneg xpos.le _)).trans
      (Real.rpow_le_rpow_of_exponent_le x1 (by linarith))
    Ibu := Nat.floor_le (Real.rpow_nonneg xpos.le _)
    hE := rfl
    hu := rfl
    hz := rfl }
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
