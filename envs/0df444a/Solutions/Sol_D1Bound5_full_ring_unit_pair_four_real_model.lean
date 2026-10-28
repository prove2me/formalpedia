-- Prove2me | solution 1 for D1Bound5.full_ring_unit_pair_four_real_model
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:08.571446+00:00
-- url     : https://prove2.me/submissions/60b99f86-e159-4b7b-8ac4-16c4a29aabb8

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions
import Theorems.Thm_D1Bound5_UnitPairArithmeticModel_four_extensions_real
import Theorems.Thm_D1Bound5_full_ring_unit_pair_arithmetic_model
import Theorems.Thm_D1Bound5_full_ring_unit_pair_even_three_real_impossible
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_unit_pair_pell_parameter_parity

section
open scoped NumberField
open Module

namespace D1Bound5







theorem unit_pair_pell_odd_parameter (d u v : ℤ)
    (hd : d % 2 ≠ 0) (h : u ^ 2 - d * v ^ 2 = 2) : d % 8 = 7 := by
  rcases unit_pair_pell_parameter_parity d u v h with h7 | h2
  · exact h7
  · omega



end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5















/-- The exact arithmetic reduction for a genuine unit-pair sextuple:
all four other entries are signed norm-two Pell magnitudes for one fixed
positive squarefree d congruent to seven modulo eight. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hm : t 0 = -1) (hp : t 1 = 1) :
    ∃ M : UnitPairArithmeticModel (𝓞 K), M.d % 8 = 7 ∧
      ∀ i : Fin 4, UnitPairRealDescription M.d (t ⟨i.val+2,by omega⟩) := by
  classical
  obtain ⟨M⟩ := full_ring_unit_pair_arithmetic_model hK
  let e : Fin 4 → Fin 6 := fun i => ⟨i.val+2,by omega⟩
  let z : Fin 4 → 𝓞 K := fun i => t (e i)
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have he (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j := by
    intro h
    apply hij
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp [e] at hh
    omega
  have hz (i : Fin 4) : z i ≠ 0 := ht.2.1 (e i)
  have hroots (i : Fin 4) :
      (∃ r : 𝓞 K, r^2 = 1-z i) ∧ (∃ r : 𝓞 K, r^2 = 1+z i) := by
    have hi0 : (0 : Fin 6) ≠ e i := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [e] at hh
      omega
    have hi1 : (1 : Fin 6) ≠ e i := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [e] at hh
      omega
    obtain ⟨r,hr⟩ := ht.2.2 0 (e i) hi0
    obtain ⟨s,hs⟩ := ht.2.2 1 (e i) hi1
    constructor
    · refine ⟨r,?_⟩
      rw [pow_two,hr,hm]
      dsimp [z]
      ring
    · exact ⟨s,by simpa only [pow_two,hp,one_mul,add_comm] using hs⟩
  have hpair (i j : Fin 4) (hij : i ≠ j) :
      ∃ r : 𝓞 K, r^2 = 1+z i*z j := by
    obtain ⟨r,hr⟩ := ht.2.2 (e i) (e j) (he i j hij)
    exact ⟨r,by simpa only [pow_two,add_comm] using hr⟩
  have hreal := M.four_extensions_real f (fun x hx => one_le_norm_integer hK phi hx)
    z hz hroots hpair
  have hodd : M.d % 2 ≠ 0 := by
    intro heven
    apply full_ring_unit_pair_even_three_real_impossible hK M.d M.positive heven
      (fun i : Fin 3 => z i.castSucc) (fun i => hreal i.castSucc)
    intro i j hij
    apply hpair i.castSucc j.castSucc
    exact fun h => hij (Fin.castSucc_injective 3 h)
  obtain ⟨u,v,_,hPell,_⟩ := hreal 0
  exact ⟨M,unit_pair_pell_odd_parameter M.d u v hodd hPell,hreal⟩



end D1Bound5
end
