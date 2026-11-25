-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:59.265667+00:00
-- url     : https://prove2.me/submissions/11e7f2f4-d465-40fb-b040-9c51efdf3deb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cF_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (N U : ℕ) (hUN : U ≤ N) :
    cF χ N = ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) +
      ∑ a ∈ Ioc 0 N, ((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) := by
  rw [cF_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUN]
  congr 1
  have hcond : ∀ (b a : ℕ), b ∈ Finset.Ioc U N ∧ a ∈ Finset.Ioc 0 (N / b) ↔
      b ∈ Finset.Ioc U (N / a) ∧ a ∈ Finset.Ioc 0 N := by
    intro b a
    simp only [Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hUb, hbN⟩, ha0, haN⟩
      have hb0 : 0 < b := by omega
      have h1 : a * b ≤ N := (Nat.le_div_iff_mul_le hb0).mp haN
      refine ⟨⟨hUb, (Nat.le_div_iff_mul_le ha0).mpr (by linarith)⟩, ha0, ?_⟩
      exact le_trans (Nat.le_mul_of_pos_right a hb0) h1
    · rintro ⟨⟨hUb, hbNa⟩, ha0, haN⟩
      have h1 : b * a ≤ N := (Nat.le_div_iff_mul_le ha0).mp hbNa
      have hb0 : 0 < b := by omega
      exact ⟨⟨hUb, le_trans (Nat.le_mul_of_pos_right b ha0) h1⟩, ha0,
        (Nat.le_div_iff_mul_le hb0).mpr (by linarith)⟩
  unfold hH
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
