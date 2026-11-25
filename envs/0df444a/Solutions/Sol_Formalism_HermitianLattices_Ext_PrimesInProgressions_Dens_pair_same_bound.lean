-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.pair_same_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:16.780014+00:00
-- url     : https://prove2.me/submissions/ad938aa6-ceeb-4a12-af87-ca5789dba595

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_sum_twist_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_sum_range_periodic_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_sum_cpow_sub_prim_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_prim_dyadic_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution : PairSame := by
  intro M _ w hw hw1 ht U hU
  have hM0 : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have h1w : 1 - w ≠ 0 := by
    intro h; apply ht
    have := congrArg Complex.im h
    simpa using this
  set c : ℂ := (Fintype.card (ZMod M)ˣ : ℂ) / (M : ℂ) with hc
  have hcn : ‖c‖ ≤ 1 := by
    rw [hc, norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hM0,
      ZMod.card_units_eq_totient]
    exact_mod_cast Nat.totient_le M
  set h : ZMod M → ℂ := fun a => (1 : DirichletCharacter ℂ M) a - c with hh
  have hK : ∀ a, ‖h a‖ ≤ 2 := by
    intro a
    refine (norm_sub_le _ _).trans ?_
    have := DirichletCharacter.norm_le_one (1 : DirichletCharacter ℂ M) a
    linarith
  have hsum0 : ∑ a : ZMod M, h a = 0 := by
    simp only [hh]
    rw [Finset.sum_sub_distrib, MulChar.sum_one_eq_card_units, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, hc]
    have : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    field_simp
    ring
  have hA := norm_sum_twist_le (fun n => h (n : ZMod M)) (m := 2 * (M : ℝ))
    (fun k => norm_sum_range_periodic_le h hK hsum0 k) hw hU
  have hB := norm_sum_cpow_sub_prim_le hU hw h1w (2 * U) (by omega)
  have hC := norm_prim_dyadic_le hU hw ht
  have hB' : ((((2 * U : ℕ) : ℝ)) - U) * (‖w‖ / U) = ‖w‖ := by
    push_cast; field_simp; ring
  rw [hB'] at hB
  have hS : ‖∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖ ≤ ‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
    have := norm_add_le (∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w) -
      (((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w))
      ((((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w))
    rw [sub_add_cancel] at this
    linarith
  have hsplit : ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) =
      ∑ n ∈ Ioc U (2 * U), h (n : ZMod M) * (n : ℂ) ^ (-w) +
        c * ∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hh]; ring
  rw [hsplit]
  have hQ : 0 ≤ (U : ℝ) ^ (1 - w.re) / |w.im| := by positivity
  have hcS : ‖c * ∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖ ≤
      ‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
    rw [norm_mul]
    calc ‖c‖ * ‖∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖
        ≤ 1 * (‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im|) :=
          mul_le_mul hcn hS (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine (norm_add_le _ _).trans ((add_le_add hA hcS).trans ?_)
  have e3 : 3 * (U : ℝ) ^ (1 - w.re) / |w.im| = 3 * ((U : ℝ) ^ (1 - w.re) / |w.im|) := by ring
  have e4 : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| = 4 * ((U : ℝ) ^ (1 - w.re) / |w.im|) := by ring
  rw [e3, e4]
  nlinarith [norm_nonneg w]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
