-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.numeric_constants
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:47.570301+00:00
-- url     : https://prove2.me/submissions/aae75052-2349-4734-9b56-959957458d66

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
attribute [local irreducible] q0 pY pJ pN
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : Num := by
  intro C hC
  have h3 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 7 / 100)).bound
    (by norm_num : (0 : ℝ) < 1 / 32768)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 47 / 50)).bound
    (by positivity : (0 : ℝ) < 1 / (65536 * (C + 1)))
  obtain ⟨Q1, hQ1⟩ := Filter.eventually_atTop.1 (h3.and h2)
  refine ⟨max 20 Q1, 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ), le_max_left _ _, fun Q hQ => ?_⟩
  have hQ20 : 20 ≤ Q := (le_max_left _ _).trans hQ
  obtain ⟨hl3, hl2⟩ := hQ1 Q ((le_max_right _ _).trans hQ)
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hQ0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog0 : 0 ≤ Real.log Q := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
    abs_of_nonneg (Real.rpow_nonneg hQ0.le _)] at hl3 hl2
  have hl3' : Real.log Q ^ 3 ≤ 1 / 32768 * Q ^ (7 / 100 : ℝ) := by
    have e : Real.log Q ^ (3 : ℝ) = Real.log Q ^ 3 := by simpa using Real.rpow_natCast (Real.log Q) 3
    rw [← e]
    exact hl3
  have hl2' : Real.log Q ^ 2 ≤ 1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ) := by
    have e : Real.log Q ^ (2 : ℝ) = Real.log Q ^ 2 := by simpa using Real.rpow_natCast (Real.log Q) 2
    rw [← e]
    exact hl2
  have hq1 : Q ≤ (q0 Q : ℝ) := by rw [q0]; exact Nat.le_ceil Q
  have hq2 : (q0 Q : ℝ) ≤ 2 * Q := by
    rw [q0]
    have := Nat.ceil_lt_add_one hQ0.le
    linarith
  have hqpos : 0 < q0 Q := by exact_mod_cast lt_of_lt_of_le hQ0 hq1
  have hL2 : 2 ^ Nat.log 2 (q0 Q) ≤ q0 Q := Nat.pow_log_le_self 2 hqpos.ne'
  have hJdef : pJ Q = 8 * (Nat.log 2 (q0 Q) + 1) := by rw [pJ]
  have hYdef : pY Q = q0 Q ^ 4 := by rw [pY]
  have hLr : (Nat.log 2 (q0 Q) : ℝ) * Real.log 2 ≤ Real.log Q + Real.log 2 := by
    have h1 : ((2 ^ Nat.log 2 (q0 Q) : ℕ) : ℝ) ≤ q0 Q := by exact_mod_cast hL2
    push_cast at h1
    have h4 : Real.log ((2 : ℝ) ^ Nat.log 2 (q0 Q)) ≤ Real.log (2 * Q) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow, Real.log_mul (by norm_num) hQ0.ne'] at h4
    linarith
  have hlt2 := Real.log_two_gt_d9
  have hlt2' := Real.log_two_lt_d9
  have hL' : (Nat.log 2 (q0 Q) : ℝ) ≤ 3 * Real.log Q := by
    by_contra hc
    push_neg at hc
    nlinarith [(Nat.cast_nonneg (Nat.log 2 (q0 Q)) : (0 : ℝ) ≤ _)]
  have hJ : (pJ Q : ℝ) ≤ 32 * Real.log Q := by
    rw [hJdef]
    push_cast
    linarith
  have hJpos : (0 : ℝ) < pJ Q := by rw [hJdef]; positivity
  constructor
  · intro j _
    have hY : Q ^ 4 ≤ ((pY Q * 2 ^ j : ℕ) : ℝ) := by
      rw [hYdef]
      push_cast
      have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      calc Q ^ 4 ≤ (q0 Q : ℝ) ^ 4 := by gcongr
        _ ≤ (q0 Q : ℝ) ^ 4 * 2 ^ j := le_mul_of_one_le_right (by positivity) h1
    have hpow : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ Q ^ (-(197 / 50 : ℝ)) := by
      calc ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ (Q ^ 4) ^ (-(197 / 200 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hY (by norm_num)
        _ = Q ^ (-(197 / 50 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
            norm_num
    have hQ3 : Q ^ 3 * Q ^ (-(197 / 50 : ℝ)) = Q ^ (-(47 / 50 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hQ0]
      norm_num
    have hQ47 : Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) = 1 := by
      rw [← Real.rpow_add hQ0]
      norm_num
    have hkey : 64 * C * (pJ Q : ℝ) ^ 2 ≤ Q ^ (47 / 50 : ℝ) := by
      have hJ2 : (pJ Q : ℝ) ^ 2 ≤ 1024 * Real.log Q ^ 2 := by nlinarith
      have hC1 : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc 64 * C * (pJ Q : ℝ) ^ 2 ≤ 64 * C * (1024 * Real.log Q ^ 2) := by gcongr
        _ ≤ 64 * C * (1024 * (1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ))) := by gcongr
        _ = C / (C + 1) * Q ^ (47 / 50 : ℝ) := by field_simp; ring
        _ ≤ 1 * Q ^ (47 / 50 : ℝ) := by gcongr
        _ = Q ^ (47 / 50 : ℝ) := one_mul _
    rw [le_div_iff₀ (by positivity)]
    calc 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2)
        ≤ 8 * Q ^ 3 * C * Q ^ (-(197 / 50 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2) := by gcongr
      _ = (64 * C * (pJ Q : ℝ) ^ 2) * (Q ^ 3 * Q ^ (-(197 / 50 : ℝ))) := by ring
      _ ≤ Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) := by rw [hQ3]; gcongr
      _ = 1 := hQ47
  · have hJ2 : (2 : ℕ) ^ pJ Q ≤ 256 * q0 Q ^ 8 := by
      rw [hJdef, pow_mul', pow_succ]
      calc (2 ^ Nat.log 2 (q0 Q) * 2) ^ 8 = 256 * (2 ^ Nat.log 2 (q0 Q)) ^ 8 := by ring
        _ ≤ 256 * q0 Q ^ 8 := by gcongr
    have hYJ : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ 1048576 * Q ^ 12 := by
      have h1 : pY Q * 2 ^ pJ Q ≤ q0 Q ^ 4 * (256 * q0 Q ^ 8) := by
        rw [hYdef]
        exact Nat.mul_le_mul_left _ hJ2
      have h4 : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := by
        exact_mod_cast h1
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := h4
        _ ≤ (2 * Q) ^ 4 * (256 * (2 * Q) ^ 8) := by gcongr
        _ = 1048576 * Q ^ 12 := by ring
    have hpow : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤
        (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (1048576 * Q ^ 12) ^ (3 / 200 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hYJ (by norm_num)
        _ = (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast Q 12,
              ← Real.rpow_mul hQ0.le]
            norm_num
    have hJ3 : (pJ Q : ℝ) ^ 3 ≤ Q ^ (7 / 100 : ℝ) := by
      calc (pJ Q : ℝ) ^ 3 ≤ (32 * Real.log Q) ^ 3 := by gcongr
        _ = 32768 * Real.log Q ^ 3 := by ring
        _ ≤ 32768 * (1 / 32768 * Q ^ (7 / 100 : ℝ)) := by gcongr
        _ = Q ^ (7 / 100 : ℝ) := by ring
    have hQ14 : 1 ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hsplit : Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ) = Q ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hQ0]
      norm_num
    calc 1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ))
        = 1 + 8 * C * ((pJ Q : ℝ) ^ 3 * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) := by ring
      _ ≤ 1 + 8 * C * (Q ^ (7 / 100 : ℝ) * ((1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ))) := by
          gcongr
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * (Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ)) := by ring
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by rw [hsplit]
      _ ≤ Q ^ (1 / 4 : ℝ) + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by gcongr
      _ = (1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ)) * Q ^ (1 / 4 : ℝ) := by ring
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
