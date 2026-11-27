-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.resid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:22:20.696458+00:00
-- url     : https://prove2.me/submissions/6840ea9d-8428-4b6e-befa-b282cde18648

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_int_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_l
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_not_mm_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_v_eq_zero_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_frob_iter
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} [NeZero d] (ψ : ZMod d → R →+* C)
    (hint : ∀ a x, V.Ge 0 (ψ a x)) (frob : ∀ a x, V.MM (ψ (a + 1) x - ψ a x ^ V.l))
    (sep : ∀ a : ZMod d, a ≠ 0 → ∃ x, ¬ V.MM (ψ a x - ψ 0 x)) (hl2 : V.l ≠ 2) :
    ∃ x : R, V.MM (ψ 0 x ^ ((V.l ^ d - 1) / 2) + 1) := by
  have hl := V.l_prime
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hl3 : 3 ≤ V.l := by have := hl.two_le; omega
  have hQ3 : 3 ≤ V.l ^ d := le_trans hl3 (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hdpos) V.l)
  have hQodd : Odd (V.l ^ d) := (hl.eq_two_or_odd'.resolve_left hl2).pow
  have hQmod : V.l ^ d % 2 = 1 := Nat.odd_iff.1 hQodd
  let P : Ideal R :=
    { carrier := {x | V.MM (ψ 0 x)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *; exact mm_add ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact mm_zero
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *; exact mm_int_mul (hint 0 c) hx }
  have hmem : ∀ x, x ∈ P ↔ V.MM (ψ 0 x) := fun x => Iff.rfl
  have hP : P.IsPrime := by
    refine ⟨?_, fun {x y} hxy => ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem, map_one]; exact not_mm_one
    · rw [hmem, map_mul] at hxy
      rw [hmem, hmem]
      by_contra hc
      push_neg at hc
      unfold VF.MM at hxy
      rw [V.v.map_mul, v_eq_zero_of (hint 0 x) hc.1, v_eq_zero_of (hint 0 y) hc.2, add_zero] at hxy
      exact lt_irrefl _ hxy
  have := hP
  have hfrobk : ∀ z : R ⧸ P, z ^ (V.l ^ d) = z := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_pow, Ideal.Quotient.eq, hmem, map_sub, map_pow]
    have h1 := frob_iter ψ hint frob x d
    rw [ZMod.natCast_self] at h1
    have e : ψ 0 x ^ (V.l ^ d) - ψ 0 x = -(ψ 0 x - ψ 0 x ^ (V.l ^ d)) := by ring
    rw [e]; exact mm_neg h1
  have hunit : ∀ z : R ⧸ P, z ≠ 0 → z ^ (V.l ^ d - 1) = 1 := by
    intro z hz
    have h1 := hfrobk z
    have e : z ^ (V.l ^ d) = z * z ^ (V.l ^ d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e] at h1
    exact mul_left_cancel₀ hz (h1.trans (mul_one z).symm)
  have hfin : Finite (R ⧸ P) := by
    have hsub : ∀ z : R ⧸ P, z ∈ insert (0 : R ⧸ P)
        (Polynomial.nthRoots (V.l ^ d - 1) (1 : R ⧸ P)).toFinset := by
      intro z
      by_cases hz : z = 0
      · rw [hz]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
        exact hunit z hz
    exact Set.finite_univ_iff.1 ((Finset.finite_toSet _).subset fun z _ => hsub z)
  have := hfin
  have hmax : P.IsMaximal := Ideal.Quotient.maximal_of_isField P (Finite.isDomain_to_isField _)
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  haveI : CharP (R ⧸ P) V.l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem, hmem, map_natCast]
    exact mm_l)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (R ⧸ P) V.l
  have hdn : d ≤ (n : ℕ) := by
    by_contra hlt
    push_neg at hlt
    have hn0 : ((n : ℕ) : ZMod d) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd n.pos hdvd
      omega
    obtain ⟨x, hx⟩ := sep _ hn0
    apply hx
    have h1 := frob_iter ψ hint frob x n
    have h2 : V.MM (ψ 0 x ^ (V.l ^ (n : ℕ)) - ψ 0 x) := by
      have := FiniteField.pow_card (Ideal.Quotient.mk P x)
      rw [hcard, ← map_pow, Ideal.Quotient.eq, hmem, map_sub, map_pow] at this
      exact this
    have e : ψ ((n : ℕ) : ZMod d) x - ψ 0 x =
        (ψ ((n : ℕ) : ZMod d) x - ψ 0 x ^ (V.l ^ (n : ℕ))) + (ψ 0 x ^ (V.l ^ (n : ℕ)) - ψ 0 x) := by ring
    rw [e]; exact mm_add h1 h2
  have hpos : 0 < (V.l ^ d - 1) / 2 := by omega
  have hm : ∃ z : R ⧸ P, z ^ ((V.l ^ d - 1) / 2) = -1 := by
    by_contra hno
    push_neg at hno
    have hsq : ∀ z : R ⧸ P, z ≠ 0 → z ^ ((V.l ^ d - 1) / 2) = 1 := by
      intro z hz
      have h2 : (z ^ ((V.l ^ d - 1) / 2)) * (z ^ ((V.l ^ d - 1) / 2)) = 1 := by
        rw [← pow_add, ← hunit z hz]; congr 1; omega
      rcases mul_self_eq_one_iff.1 h2 with h | h
      · exact h
      · exact absurd h (hno z)
    have hsub : (Finset.univ : Finset (R ⧸ P)) ⊆
        insert 0 (Polynomial.nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P)).toFinset := by
      intro z _
      by_cases hz : z = 0
      · rw [hz]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (by
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hpos]; exact hsq z hz)
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_insert_le (0 : R ⧸ P)
      (Polynomial.nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P)).toFinset
    have hc3 := Multiset.toFinset_card_le (Polynomial.nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P))
    have hc4 := Polynomial.card_nthRoots ((V.l ^ d - 1) / 2) (1 : R ⧸ P)
    rw [Finset.card_univ, hcard] at hc1
    have hpow : V.l ^ d ≤ V.l ^ (n : ℕ) := Nat.pow_le_pow_right hl.pos hdn
    omega
  obtain ⟨z, hz⟩ := hm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨x, ?_⟩
  have h1 : Ideal.Quotient.mk P (x ^ ((V.l ^ d - 1) / 2) + 1) = 0 := by
    rw [map_add, map_pow, hz, map_one, neg_add_cancel]
  have h2 := (hmem _).1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  rwa [map_add, map_pow, map_one] at h2
end Formalism.L2.FormalSeriesBounds.GmExArith
