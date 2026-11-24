-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_norm_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:22.262847+00:00
-- url     : https://prove2.me/submissions/a09a1594-2a50-4dc3-88e9-36a5ea4b3767

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_card_fibers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (h2 : finrank K L = 2) (d : K) (hd : d ≠ 0) :
    (Nat.card {y : L // Algebra.norm K y = d} : ℤ) = Fintype.card K + 1 := by
  classical
  have heq : ∀ d' : K, d' ≠ 0 →
      Nat.card {y : L // Algebra.norm K y = d'} = Nat.card {y : L // Algebra.norm K y = d} := by
    intro d' hd'
    obtain ⟨u, hu⟩ := FiniteField.norm_surjective K L (d / d')
    have hu0 : u ≠ 0 := by
      rintro rfl; rw [Algebra.norm_eq_zero_iff.mpr rfl] at hu; exact div_ne_zero hd hd' hu.symm
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft₀ u hu0) (fun y => ?_))
    show Algebra.norm K y = d' ↔ Algebra.norm K (u * y) = d
    rw [map_mul, hu]
    constructor
    · intro h; rw [h]; field_simp
    · intro h; field_simp at h; exact h
  have h0 : Nat.card {y : L // Algebra.norm K y = (0 : K)} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, Algebra.norm_eq_zero_iff.mpr rfl⟩⟩⟩
    rw [Algebra.norm_eq_zero_iff.mp a.2, Algebra.norm_eq_zero_iff.mp b.2]
  have htot := s5a4_card_fibers (fun y : L => Algebra.norm K y)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), h0,
    Finset.sum_congr rfl (fun k hk => by rw [heq k (Finset.ne_of_mem_erase hk)]),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Module.card_eq_pow_finrank (K := K) (V := L), h2] at htot
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  set q := Fintype.card K
  set n := Nat.card {y : L // Algebra.norm K y = d}
  rw [nsmul_eq_mul] at htot
  push_cast [Nat.cast_sub hq.le] at htot
  have hq' : ((q : ℤ) - 1) ≠ 0 := by
    have : (1 : ℤ) < q := by exact_mod_cast hq
    omega
  apply mul_left_cancel₀ hq'
  linear_combination htot
end Formalism.HermitianLatticeCounting.P
