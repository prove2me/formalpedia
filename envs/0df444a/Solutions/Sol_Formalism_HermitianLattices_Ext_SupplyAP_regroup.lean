-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.regroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:34.576871+00:00
-- url     : https://prove2.me/submissions/11dc13fc-36a1-4e23-8aad-10cec5a9b152

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d (d * m) := by
  have h1 : ∀ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, if d ∣ n then F d n else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    constructor
    · rintro ⟨hdn, hn0⟩
      have := Nat.le_of_dvd (by omega) hdn
      have := Nat.pos_of_dvd_of_pos hdn (by omega)
      exact ⟨⟨by omega, by omega⟩, hdn⟩
    · rintro ⟨_, hdn⟩
      exact ⟨hdn, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← Finset.sum_filter]
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  symm
  refine Finset.sum_nbij (fun m => d * m) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, Dvd.intro _ rfl⟩
    calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d hm.2
      _ ≤ N := Nat.mul_div_le N d
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd1 hab
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
    obtain ⟨⟨hn1, hnN⟩, m, rfl⟩ := hn
    refine ⟨m, ?_, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hn1), ?_⟩
    exact (Nat.le_div_iff_mul_le hd1).mpr (by rw [Nat.mul_comm]; exact hnN)
end Formalism.HermitianLattices.Ext.SupplyAP
