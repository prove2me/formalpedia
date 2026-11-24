-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_herm_rec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:34.472026+00:00
-- url     : https://prove2.me/submissions/803f4b10-7669-4b93-8d82-c8302760e38e

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_sum_fiber
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_card_fibers
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_norm_fiber

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
    (h2 : finrank K L = 2) (M : ℕ) (c : K) :
    (Nat.card {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) =
      (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) +
      ((Fintype.card K : ℤ) + 1) * ((Fintype.card K : ℤ) ^ (2 * M) -
        (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ)) := by
  classical
  let A : K → ℤ := fun c => (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ)
  have e1 : {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} ≃
      {p : L × (Fin M → L) // ∑ i, Algebra.norm K (p.2 i) = c - Algebra.norm K p.1} :=
    Equiv.subtypeEquiv (Fin.consEquiv (fun _ => L)).symm (fun x => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail]
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring)
  have s1 : (Nat.card {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) =
      ∑ y : L, A (c - Algebra.norm K y) := by
    rw [Nat.card_congr e1, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a : L) (b : Fin M → L) => ∑ i, Algebra.norm K (b i) = c - Algebra.norm K a)),
      Nat.card_sigma]
    push_cast; rfl
  have s2 := s5a4_sum_fiber (fun y : L => Algebra.norm K y) (fun d => A (c - d))
  have h0 : Nat.card {y : L // Algebra.norm K y = (0 : K)} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, Algebra.norm_eq_zero_iff.mpr rfl⟩⟩⟩
    rw [Algebra.norm_eq_zero_iff.mp a.2, Algebra.norm_eq_zero_iff.mp b.2]
  have s3 : ∑ d : K, A (c - d) = (Fintype.card K : ℤ) ^ (2 * M) := by
    have hc := Equiv.sum_comp (Equiv.subLeft c) A
    simp only [Equiv.subLeft_apply] at hc
    rw [hc]
    have := s5a4_card_fibers (fun x : Fin M → L => ∑ i, Algebra.norm K (x i))
    rw [this, Fintype.card_fun, Fintype.card_fin, Module.card_eq_pow_finrank (K := K) (V := L), h2]
    push_cast; ring
  rw [s1, s2, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), h0,
    Finset.sum_congr rfl (fun k hk => by rw [s5a4_norm_fiber h2 k (Finset.ne_of_mem_erase hk)]),
    ← Finset.mul_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))] at s3
  simp only [sub_zero] at s3 ⊢
  have : ∑ x ∈ Finset.univ.erase (0 : K), A (c - x) = (Fintype.card K : ℤ) ^ (2 * M) - A c := by
    linear_combination s3
  rw [this]; simp [A]
end Formalism.HermitianLatticeCounting.P
