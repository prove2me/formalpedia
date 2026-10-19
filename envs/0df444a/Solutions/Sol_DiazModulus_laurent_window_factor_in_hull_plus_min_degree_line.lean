-- Prove2me | solution 1 for DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:49:11.366984+00:00
-- url     : https://prove2.me/submissions/71db4aea-f8c6-4c48-827e-31d5b3a51549

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Width count: a factor of the lower pencil member lies in `H_N` plus the line of least degree

Let `H = span(X^(N-1), X^N, X^(N+1))`, `M` a plane all of whose non-zero elements have degree
at least `N + 2`, and `n ∈ M` non-zero of least degree. Suppose `deg p < deg q` and
`p y = h + m`, `q y = h' + m'` with `h, h' ∈ H` and `m, m' ∈ M`. If `m = 0` there is nothing to
prove. Otherwise `deg (p y) = deg m ≥ N + 2 > deg h`, so `p, y ≠ 0` and
`deg (q y) > deg (p y) ≥ N + 2`; hence `m' ≠ 0` and `deg (q y) = deg m'`, so `deg m < deg m'`.
Two elements of distinct degrees span the plane `M`, so `n = a m + b m'`; minimality of
`deg n` forces `b = 0`, so `m ∈ K n` and `p y ∈ span(H, n)`.
-/

open Polynomial

namespace R18_L2

open DiazModulus

variable {K : Type*} [Field K]

/-- Two polynomials of distinct degrees, the lower one non-zero, span a plane. -/
theorem finrank_pair {p q : K[X]} (hp : p ≠ 0) (hpq : p.natDegree < q.natDegree) :
    Module.finrank K (Submodule.span K ({p, q} : Set K[X])) = 2 := by
  have hq : q ≠ 0 := by rintro rfl; simp at hpq
  have hli : LinearIndependent K ![p, q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have := congrArg (fun f => f.coeff q.natDegree) hst
      simpa [coeff_eq_zero_of_natDegree_lt hpq, hq] using this
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hp, rfl⟩
  have := finrank_span_eq_card hli
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this

/-- Elements of the window `H_N` have degree at most `N + 1`. -/
theorem window_natDegree_le {N : ℕ} {h : K[X]}
    (hh : h ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X])) :
    h.natDegree ≤ N + 1 := by
  have hle : Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ≤
      degreeLE K (N + 1) := by
    rw [Submodule.span_le]
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rw [SetLike.mem_coe, mem_degreeLE]
    rcases hf with rfl | rfl | rfl <;>
      exact (degree_X_pow_le _).trans (by exact_mod_cast (by omega))
  exact natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp (hle hh))

end R18_L2

open DiazModulus R18_L2 in
open Polynomial in
theorem solution (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X])
    (hM2 : Module.finrank K M = 2)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree) :
    ∃ n ∈ M, n ≠ 0 ∧ (∀ f ∈ M, f ≠ 0 → n.natDegree ≤ f.natDegree) ∧
      ∀ p q y : K[X], p.natDegree < q.natDegree → p * y ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) →
        q * y ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) →
        p * y ∈ Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1), n} : Set K[X]) := by
  classical
  have : FiniteDimensional K M := Module.finite_of_finrank_pos (by omega)
  -- `M` has a non-zero element; take one of least degree
  have hex : ∃ k, ∃ f ∈ M, f ≠ 0 ∧ f.natDegree = k := by
    by_contra hcon
    have hbot : M = ⊥ := (Submodule.eq_bot_iff M).mpr fun f hf => by
      by_contra hf0; exact hcon ⟨_, f, hf, hf0, rfl⟩
    rw [hbot, finrank_bot] at hM2
    exact absurd hM2 (by norm_num)
  obtain ⟨n, hnM, hn0, hnk⟩ := Nat.find_spec hex
  have hmin : ∀ f ∈ M, f ≠ 0 → n.natDegree ≤ f.natDegree := by
    intro f hf hf0; rw [hnk]; exact Nat.find_min' hex ⟨f, hf, hf0, rfl⟩
  refine ⟨n, hnM, hn0, hmin, ?_⟩
  intro p q y hpq hpy hqy
  set S := Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1), n} : Set K[X]) with hS
  have hsub : Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ≤ S :=
    Submodule.span_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hnS : n ∈ S := Submodule.subset_span (by simp)
  obtain ⟨h, hh, m, hm, hhm⟩ := Submodule.mem_sup.mp hpy
  by_cases hm0 : m = 0
  · rw [← hhm, hm0, add_zero]; exact hsub hh
  have hmd := hMd m hm hm0
  have hhd := window_natDegree_le hh
  have hpyd : (p * y).natDegree = m.natDegree := by
    rw [← hhm]; exact natDegree_add_eq_right_of_natDegree_lt (by omega)
  have hpy0 : p * y ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hpyd; omega
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hpy0
  have hy0 : y ≠ 0 := right_ne_zero_of_mul hpy0
  have hq0 : q ≠ 0 := by rintro rfl; simp at hpq
  have hqyd : (p * y).natDegree < (q * y).natDegree := by
    rw [natDegree_mul hp0 hy0, natDegree_mul hq0 hy0]; omega
  obtain ⟨h', hh', m', hm', hhm'⟩ := Submodule.mem_sup.mp hqy
  have hhd' := window_natDegree_le hh'
  have hm'0 : m' ≠ 0 := by
    rintro rfl; rw [add_zero] at hhm'; rw [← hhm'] at hqyd; omega
  have hmd' := hMd m' hm' hm'0
  have hqyd' : (q * y).natDegree = m'.natDegree := by
    rw [← hhm']; exact natDegree_add_eq_right_of_natDegree_lt (by omega)
  have hmm' : m.natDegree < m'.natDegree := by omega
  -- `M = span(m, m')`
  have hMeq : Submodule.span K ({m, m'} : Set K[X]) = M := by
    refine Submodule.eq_of_le_of_finrank_le ?_ (by rw [finrank_pair hm0 hmm', hM2])
    rw [Submodule.span_le]
    intro f hf
    rcases hf with rfl | rfl
    · exact hm
    · exact hm'
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hMeq ▸ hnM)
  have hb : b = 0 := by
    by_contra hb
    have hdeg : n.natDegree = m'.natDegree := by
      rw [← hab, natDegree_add_eq_right_of_natDegree_lt]
      · exact natDegree_smul m' hb
      · rw [natDegree_smul m' hb]; exact (natDegree_smul_le _ _).trans_lt hmm'
    have := hmin m hm hm0
    omega
  rw [hb, zero_smul, add_zero] at hab
  have ha : a ≠ 0 := by rintro rfl; rw [zero_smul] at hab; exact hn0 hab.symm
  have hmn : m = a⁻¹ • n := by rw [← hab, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [← hhm, hmn]
  exact S.add_mem (hsub hh) (S.smul_mem _ hnS)
