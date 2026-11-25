-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:38.096608+00:00
-- url     : https://prove2.me/submissions/53797778-017d-487f-86ea-a9ac8f7119a4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA

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
theorem _root_.solution (N : ℕ) :
    cF χ N = ∑ b ∈ Ioc 0 N, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) := by
  have hcond : ∀ (n d : ℕ), n ∈ Finset.Ioc 0 N ∧ d ∈ n.divisors ↔
      n ∈ (Finset.Ioc 0 N).filter (d ∣ ·) ∧ d ∈ Finset.Ioc 0 N := by
    intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, -⟩
      have h1 := Nat.le_of_dvd hn0 hdn
      have h2 := Nat.pos_of_dvd_of_pos hdn hn0
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, h2, by omega⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩
      exact ⟨⟨hn0, hnN⟩, hdn, by omega⟩
  unfold cF hH
  simp only [Finset.sum_div]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
  have himg : (Finset.Ioc 0 N).filter (d ∣ ·) = (Finset.Ioc 0 (N / d)).image (fun a => d * a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨a, rfl⟩⟩
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos a with h | h
        · subst h
          simp at h1
        · exact h
      · exact (Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd0 h1, ?_⟩, dvd_mul_right d a⟩
      have h3 := (Nat.le_div_iff_mul_le hd0).mp h2
      rw [mul_comm]
      exact h3
  rw [himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : (a : ℂ) ≠ 0 := by
    have h1 := (Finset.mem_Ioc.mp ha).1
    exact_mod_cast h1.ne'
  have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
