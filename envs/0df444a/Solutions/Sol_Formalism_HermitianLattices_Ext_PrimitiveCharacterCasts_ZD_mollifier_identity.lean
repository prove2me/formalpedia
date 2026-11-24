-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mollifier_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.753632+00:00
-- url     : https://prove2.me/submissions/72b5acf5-f8a7-4c14-9278-7fe06607005b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : MollId := by
  unfold MollId
  intro q _ χ s Y N K hY hYN hK
  have hN : 1 ≤ N := le_trans hY hYN
  have hYK : Y ≤ K := by
    calc Y = Y * 1 := (mul_one Y).symm
      _ ≤ Y * N := Nat.mul_le_mul le_rfl hN
      _ ≤ K := hK
  have hmaps : ∀ p ∈ Icc 1 Y ×ˢ Icc 1 N, p.1 * p.2 ∈ Icc 1 K := by
    intro p hp
    simp only [mem_product, mem_Icc] at hp ⊢
    constructor
    · have := Nat.mul_le_mul hp.1.1 hp.2.1
      simpa using this
    · exact le_trans (Nat.mul_le_mul hp.1.2 hp.2.2) hK
  rw [sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm, ← sum_product',
    ← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 K) hmaps]
  calc _ = ∑ k ∈ Icc 1 K, mco Y N k * χ k * (k : ℂ) ^ (-s) := by
        apply sum_congr rfl
        intro k _
        unfold mco
        rw [sum_mul, sum_mul]
        apply sum_congr rfl
        intro p hp
        rw [mem_filter] at hp
        obtain ⟨-, hpk⟩ := hp
        subst hpk
        simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
        ring
    _ = 1 + ∑ n ∈ Ioc Y K, mco Y N n * χ n * (n : ℂ) ^ (-s) := by
        have hsplit : Icc 1 K = Icc 1 Y ∪ Ioc Y K := by
          ext k
          simp only [mem_union, mem_Icc, mem_Ioc]
          omega
        have hdisj : Disjoint (Icc 1 Y) (Ioc Y K) := by
          rw [disjoint_left]
          intro k hk hk'
          rw [mem_Icc] at hk
          rw [mem_Ioc] at hk'
          omega
        rw [hsplit, sum_union hdisj]
        congr 1
        rw [sum_eq_single 1]
        · rw [mco_one hY hN]
          simp
        · intro k hk hk1
          rw [mem_Icc] at hk
          rw [mco_eq_zero (by omega) hk.2 hYN]
          simp
        · intro h
          exact absurd (mem_Icc.mpr ⟨le_rfl, hY⟩) h
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
