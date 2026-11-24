-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:23.726722+00:00
-- url     : https://prove2.me/submissions/448c9453-5c81-44c1-b5ce-0b588d2bf1e0

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exponent_inequality_degenerate_mid
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exponent_inequality_degenerate_top
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pow_eq_exp_mul_log
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_parameterRange_bounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_commonFactor_nonneg_and_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_massRatio_bound_of_mid
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_massRatio_bound_of_top
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_two_div_pow_eq_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DegSum := by
  unfold DegSum
  intro C hC
  refine ⟨16 * C ^ 32, ?_⟩
  intro k m f b g v NT Gam Xi hPar hXi
  obtain ⟨hm4, hmf, hfk, hlb, hlk, hlC0, hlC, hlg, hl20, hl2, hX, hg0, hb0, hv0, hlv, hNT0, hlNT,
    hGam0, hlG0, hlG⟩ := parameterRange_bounds C hC k m f b g v NT Gam hPar
  have hk0 : (0 : ℝ) < k := by linarith
  have hk0' : (k : ℝ) ≠ 0 := hk0.ne'
  have hC0 : 0 < C := by linarith
  have hf1 : 1 ≤ f := by exact_mod_cast (show (1 : ℝ) ≤ f by linarith)
  have hfkN : f ≤ k := by exact_mod_cast hfk
  have hk1 : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
  have hkexp : ∀ X : ℝ, (k : ℝ) * Real.exp (X - Real.log k) = Real.exp X := fun X => by
    rw [Real.exp_sub, Real.exp_log hk0]
    field_simp
  have hrow : ∀ s ∈ Finset.Icc 2 k, degRow C k m f s b g v Gam Xi ≤ Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨hs2, hsk⟩ := hs
    have hrowEq : degRow C k m f s b g v Gam Xi =
        (2 / g) ^ ((s - 2) * k * f) * commonLatticeBound C k m f s b v Gam Xi *
          Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f) := by
      unfold degRow commonLatticeBound
      ring
    have hcast : (((s - 2) * k * f : ℕ) : ℝ) = ((s : ℝ) - 2) * k * f := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ s), Nat.cast_ofNat]
    have hCk : (C / k) ^ (k * f) = Real.exp ((k : ℝ) * f * (Real.log C - Real.log k)) := by
      rw [pow_eq_exp_mul_log _ (div_pos hC0 hk0), Real.log_div hC0.ne' hk0', Nat.cast_mul]
    have hs2R : (2 : ℝ) ≤ s := by exact_mod_cast hs2
    have hskR : (s : ℝ) ≤ k := by exact_mod_cast hsk
    rw [hrowEq, two_div_pow_eq_exp g hg0, hcast, hCk]
    rcases (show s + 2 ≤ k ∨ (s + 1 = k ∨ s = k) by omega) with hmid | htop
    · obtain ⟨hXi0, hA⟩ := massRatio_bound_of_mid C hC k m f s b v NT Xi hb0 hXi hs2 hmid
      obtain ⟨-, hc⟩ := commonFactor_nonneg_and_le C hC k m f s b v Gam Xi _ hb0 hv0 hGam0 (by omega) hsk hf1 hfkN hXi0 hA
      have hcore := exponent_inequality_degenerate_mid C k f m (Real.log b) (Real.log k) (Real.log g) (Real.log C) (Real.log 2) hC hm4 hmf
        hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX s (Real.log Gam) hs2R hskR hlG0 hlG
      refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (Real.exp_pos _).le) (Real.exp_pos _).le) ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    · have hKS : (k : ℝ) - 1 ≤ s := by
        have h1 : k ≤ s + 1 := by omega
        have h2 : (k : ℝ) ≤ s + 1 := by exact_mod_cast h1
        linarith
      obtain ⟨hXi0, hA⟩ := massRatio_bound_of_top C hC k m f s b v NT Xi hb0 hv0 hNT0 hk1 hlv hlNT hXi htop
      obtain ⟨-, hc⟩ := commonFactor_nonneg_and_le C hC k m f s b v Gam Xi _ hb0 hv0 hGam0 (by omega) hsk hf1 hfkN hXi0 hA
      have hcore := exponent_inequality_degenerate_top C k f m (Real.log b) (Real.log k) (Real.log g) (Real.log C) (Real.log 2) hC hm4 hmf
        hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX s (Real.log Gam) hs2R hskR hKS hlG0 hlG
      refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (Real.exp_pos _).le) (Real.exp_pos _).le) ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
  calc _ ≤ ∑ s ∈ Finset.Icc 2 k, Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := Finset.sum_le_sum hrow
    _ = ((Finset.Icc 2 k).card : ℝ) * Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [Nat.card_Icc]
        exact_mod_cast (by omega : k + 1 - 2 ≤ k)
    _ = Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam) := hkexp _
    _ = Real.exp (-((k : ℝ) * f * Real.log k) / 2) * (Gam ^ 2)⁻¹ := by
        rw [Real.exp_sub, pow_eq_exp_mul_log Gam hGam0 2, div_eq_mul_inv, Nat.cast_ofNat]
end Formalism.HermitianLatticeCounting.P
