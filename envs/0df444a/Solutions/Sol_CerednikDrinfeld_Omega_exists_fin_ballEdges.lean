-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_fin_ballEdges
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/58dd70f9-89d9-5b90-a4a0-3dbde7ae3e03

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_fin_ballEdges

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace BallEdgesL2

variable {R : Type} [CommRing R] (K₀ : Type) [Field K₀] [Algebra R K₀] (ϖ₀ : R)

theorem finite_quot_pow [Finite (R ⧸ Ideal.span {ϖ₀})] (e : ℕ) : Finite (R ⧸ Ideal.span {ϖ₀ ^ e}) := by
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton ϖ₀) e

open scoped Classical in

noncomputable def rep (e : ℕ) (q : R ⧸ Ideal.span {ϖ₀ ^ e}) : R :=
  if q = 0 then 0 else (Ideal.Quotient.mk_surjective q).choose

theorem mk_rep (e : ℕ) (q : R ⧸ Ideal.span {ϖ₀ ^ e}) :
    Ideal.Quotient.mk (Ideal.span {ϖ₀ ^ e}) (rep ϖ₀ e q) = q := by
  unfold rep
  split_ifs with h
  · rw [h, map_zero]
  · exact (Ideal.Quotient.mk_surjective q).choose_spec

theorem rep_zero (e : ℕ) : rep ϖ₀ e (0 : R ⧸ Ideal.span {ϖ₀ ^ e}) = 0 := by
  simp [rep]

theorem rep_injective (e : ℕ) : Function.Injective (rep ϖ₀ e) := fun q q' h => by
  rw [← mk_rep ϖ₀ e q, ← mk_rep ϖ₀ e q', h]

@[reducible] noncomputable def fint [Finite (R ⧸ Ideal.span {ϖ₀})] (e : ℕ) : Fintype (R ⧸ Ideal.span {ϖ₀ ^ e}) :=
  @Fintype.ofFinite _ (finite_quot_pow ϖ₀ e)

open scoped Classical in

noncomputable def qlist [Finite (R ⧸ Ideal.span {ϖ₀})] (e : ℕ) : List (R ⧸ Ideal.span {ϖ₀ ^ e}) :=
  0 :: ((@Finset.univ _ (fint ϖ₀ e)).erase 0).toList

theorem mem_qlist [Finite (R ⧸ Ideal.span {ϖ₀})] (e : ℕ) (q : R ⧸ Ideal.span {ϖ₀ ^ e}) : q ∈ qlist ϖ₀ e := by
  classical
  unfold qlist
  by_cases h : q = 0
  · rw [h]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (Finset.mem_toList.2 (Finset.mem_erase.2 ⟨h, @Finset.mem_univ _ (fint ϖ₀ e) _⟩))

theorem nodup_qlist [Finite (R ⧸ Ideal.span {ϖ₀})] (e : ℕ) : (qlist ϖ₀ e).Nodup := by
  classical
  unfold qlist
  refine List.nodup_cons.2 ⟨fun h => ?_, Finset.nodup_toList _⟩
  exact (Finset.mem_erase.1 (Finset.mem_toList.1 h)).1 rfl

noncomputable def entry (n e : ℕ) (q : R ⧸ Ideal.span {ϖ₀ ^ e}) : K₀ × ℤ :=
  (algebraMap R K₀ (rep ϖ₀ e q) / algebraMap R K₀ ϖ₀ ^ n, (e : ℤ) - n)

noncomputable def block [Finite (R ⧸ Ideal.span {ϖ₀})] (n e : ℕ) : List (K₀ × ℤ) :=
  (qlist ϖ₀ e).map (entry K₀ ϖ₀ n e)

noncomputable def blist [Finite (R ⧸ Ideal.span {ϖ₀})] (n : ℕ) : List (K₀ × ℤ) :=
  ((List.range (2 * n)).map (fun i => block K₀ ϖ₀ n (i + 1))).flatten

theorem mem_blist_iff [Finite (R ⧸ Ideal.span {ϖ₀})] (n : ℕ) (p : K₀ × ℤ) :
    p ∈ blist K₀ ϖ₀ n ↔ ∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 * n ∧ ∃ q : R ⧸ Ideal.span {ϖ₀ ^ e}, p = entry K₀ ϖ₀ n e q := by
  constructor
  · intro hp
    rw [blist, List.mem_flatten] at hp
    obtain ⟨l, hl, hpl⟩ := hp
    rw [List.mem_map] at hl
    obtain ⟨i, hi, hil⟩ := hl
    rw [List.mem_range] at hi
    rw [← hil, block, List.mem_map] at hpl
    obtain ⟨q, -, hq⟩ := hpl
    exact ⟨i + 1, by omega, by omega, q, hq.symm⟩
  · rintro ⟨e, he1, he2, q, rfl⟩
    rw [blist, List.mem_flatten]
    refine ⟨block K₀ ϖ₀ n e, ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨e - 1, List.mem_range.2 (by omega), by rw [Nat.sub_add_cancel he1]⟩
    · rw [block, List.mem_map]
      exact ⟨q, mem_qlist ϖ₀ e q, rfl⟩

theorem blist_pairwise [Finite (R ⧸ Ideal.span {ϖ₀})] (n : ℕ) :
    (blist K₀ ϖ₀ n).Pairwise (fun p p' => p.2 ≤ p'.2) := by
  rw [blist, List.pairwise_flatten]
  constructor
  · intro l hl
    obtain ⟨i, -, hil⟩ := List.mem_map.1 hl
    rw [← hil, block, List.pairwise_map]
    exact List.pairwise_of_forall (fun _ _ => le_rfl)
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp ?_
    intro i j hij x hx y hy
    obtain ⟨q, -, hqx⟩ := List.mem_map.1 hx
    obtain ⟨q', -, hqy⟩ := List.mem_map.1 hy
    rw [← hqx, ← hqy]
    simp only [entry]
    push_cast
    omega

theorem entry_injective (n e : ℕ) (hπ : algebraMap R K₀ ϖ₀ ≠ 0) (hinj : Function.Injective (algebraMap R K₀)) :
    Function.Injective (entry K₀ ϖ₀ n e) := by
  intro q q' h
  have h1 := congrArg Prod.fst h
  simp only [entry] at h1
  rw [div_left_inj' (pow_ne_zero n hπ)] at h1
  exact rep_injective ϖ₀ e (hinj h1)

theorem blist_nodup [Finite (R ⧸ Ideal.span {ϖ₀})] (n : ℕ) (hπ : algebraMap R K₀ ϖ₀ ≠ 0)
    (hinj : Function.Injective (algebraMap R K₀)) : (blist K₀ ϖ₀ n).Nodup := by
  rw [blist, List.nodup_flatten]
  constructor
  · intro l hl
    obtain ⟨i, -, hil⟩ := List.mem_map.1 hl
    rw [← hil]
    exact (nodup_qlist ϖ₀ (i + 1)).map (entry_injective K₀ ϖ₀ n (i + 1) hπ hinj)
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp ?_
    intro i j hij x hx hy
    obtain ⟨q, -, hqx⟩ := List.mem_map.1 hx
    obtain ⟨q', -, hq'⟩ := List.mem_map.1 hy
    have := congrArg Prod.snd (hq'.trans hqx.symm)
    simp only [entry] at this
    omega

theorem blist_eq_cons [Finite (R ⧸ Ideal.span {ϖ₀})] (n : ℕ) (hn : 1 ≤ n) :
    ∃ t, blist K₀ ϖ₀ n = ((0 : K₀), (1 : ℤ) - n) :: t := by
  obtain ⟨N, hN⟩ : ∃ N, 2 * n = N + 1 := ⟨2 * n - 1, by omega⟩
  rw [← List.head?_eq_some_iff, blist, hN, List.range_succ_eq_map, List.map_cons, List.flatten_cons, block, qlist,
    List.map_cons, List.cons_append, List.head?_cons, entry, rep_zero, map_zero, zero_div, Nat.zero_add, Nat.cast_one]

theorem sub_div_zpow (π a b : K₀) (hπ : π ≠ 0) (n e : ℕ) :
    (a / π ^ n - b / π ^ n) / π ^ ((e : ℤ) - n) = (a - b) / π ^ e := by
  rw [← sub_div, div_div, ← zpow_natCast π n, ← zpow_add₀ hπ, show (n : ℤ) + ((e : ℤ) - n) = e by ring,
    zpow_natCast]

theorem isInteger_div_pow_iff (hπ : algebraMap R K₀ ϖ₀ ≠ 0) (hinj : Function.Injective (algebraMap R K₀))
    (d : R) (e : ℕ) :
    IsLocalization.IsInteger R (algebraMap R K₀ d / algebraMap R K₀ ϖ₀ ^ e) ↔ d ∈ Ideal.span {ϖ₀ ^ e} := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    rw [eq_div_iff (pow_ne_zero e hπ), ← map_pow, ← map_mul] at hy
    exact ⟨y, by rw [← hinj hy, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero e hπ)]

end BallEdgesL2

open BallEdgesL2 in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) [Finite (R ⧸ Ideal.span {ϖ₀})]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (k : ℕ) (cen : Fin (k + 1) → K₀) (lev : Fin (k + 1) → ℤ),
      cen 0 = 0 ∧ lev 0 = 1 - (n : ℤ) ∧
      (∀ i j, i ≤ j → lev i ≤ lev j) ∧
      (∀ i j, i ≠ j → lev i = lev j → ¬ IsLocalization.IsInteger R ((cen i - cen j) / algebraMap R K₀ ϖ₀ ^ lev j)) ∧
      (∀ j, lev j = 1 - (n : ℤ) ∨
        ∃ i, i < j ∧ lev i = lev j - 1 ∧ IsLocalization.IsInteger R ((cen j - cen i) / algebraMap R K₀ ϖ₀ ^ (lev j - 1))) ∧
      (∀ j, (1 - (n : ℤ) ≤ lev j ∧ lev j ≤ (n : ℤ) ∧ IsLocalization.IsInteger R (cen j * algebraMap R K₀ ϖ₀ ^ n))) ∧
      (∀ (c : K₀) (m : ℤ), (1 - (n : ℤ) ≤ m ∧ m ≤ (n : ℤ) ∧ IsLocalization.IsInteger R (c * algebraMap R K₀ ϖ₀ ^ n)) →
        ∃ j, lev j = m ∧ IsLocalization.IsInteger R ((c - cen j) / algebraMap R K₀ ϖ₀ ^ m)) := by
  classical
  have hinj : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  have hπ : algebraMap R K₀ ϖ₀ ≠ 0 := fun h => hϖ₀.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨t, ht⟩ := blist_eq_cons K₀ ϖ₀ n hn

  have hlen : 0 < (blist K₀ ϖ₀ n).length := by rw [ht]; exact Nat.succ_pos _
  have hidx : ∀ j : Fin ((blist K₀ ϖ₀ n).length - 1 + 1), (j : ℕ) < (blist K₀ ϖ₀ n).length := fun j => by
    have := j.2; omega
  have hmem : ∀ j : Fin ((blist K₀ ϖ₀ n).length - 1 + 1), ∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 * n ∧
      ∃ q : R ⧸ Ideal.span {ϖ₀ ^ e}, (blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j) = entry K₀ ϖ₀ n e q := fun j =>
    (mem_blist_iff K₀ ϖ₀ n _).1 (List.getElem_mem _)

  have h2 : ∀ i j : Fin ((blist K₀ ϖ₀ n).length - 1 + 1), i ≤ j →
      ((blist K₀ ϖ₀ n)[(i : ℕ)]'(hidx i)).2 ≤ ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).2 := by
    intro i j hij
    rcases (Fin.le_def.1 hij).eq_or_lt with h | h
    · have : i = j := Fin.ext h
      subst this; exact le_rfl
    · exact List.pairwise_iff_getElem.1 (blist_pairwise K₀ ϖ₀ n) _ _ (hidx i) (hidx j) h

  have h5 : ∀ j : Fin ((blist K₀ ϖ₀ n).length - 1 + 1),
      1 - (n : ℤ) ≤ ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).2 ∧ ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).2 ≤ (n : ℤ) ∧
      IsLocalization.IsInteger R (((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).1 * algebraMap R K₀ ϖ₀ ^ n) := by
    intro j
    obtain ⟨e, he1, he2, q, hq⟩ := hmem j
    rw [hq]
    simp only [entry]
    refine ⟨by omega, by omega, ⟨rep ϖ₀ e q, ?_⟩⟩
    rw [div_mul_cancel₀ _ (pow_ne_zero n hπ)]

  have h6 : ∀ (c : K₀) (m : ℤ), (1 - (n : ℤ) ≤ m ∧ m ≤ (n : ℤ) ∧
      IsLocalization.IsInteger R (c * algebraMap R K₀ ϖ₀ ^ n)) →
      ∃ j : Fin ((blist K₀ ϖ₀ n).length - 1 + 1), ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).2 = m ∧
        IsLocalization.IsInteger R ((c - ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).1) / algebraMap R K₀ ϖ₀ ^ m) := by
    rintro c m ⟨hm1, hm2, ⟨x, hx⟩⟩
    obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = m + n := ⟨(m + n).toNat, Int.toNat_of_nonneg (by omega)⟩
    have he1 : 1 ≤ e := by omega
    have he2 : e ≤ 2 * n := by omega
    have hm : m = (e : ℤ) - n := by omega
    have hc : c = algebraMap R K₀ x / algebraMap R K₀ ϖ₀ ^ n := by
      rw [eq_div_iff (pow_ne_zero n hπ)]; exact hx.symm
    set q : R ⧸ Ideal.span {ϖ₀ ^ e} := Ideal.Quotient.mk _ x with hqdef
    have hp : entry K₀ ϖ₀ n e q ∈ blist K₀ ϖ₀ n := (mem_blist_iff K₀ ϖ₀ n _).2 ⟨e, he1, he2, q, rfl⟩
    obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem hp
    refine ⟨⟨j, by omega⟩, ?_, ?_⟩
    · show ((blist K₀ ϖ₀ n)[j]'_).2 = m
      rw [hjp, entry, hm]
    · show IsLocalization.IsInteger R ((c - ((blist K₀ ϖ₀ n)[j]'_).1) / algebraMap R K₀ ϖ₀ ^ m)
      rw [hjp, entry, hc, hm, sub_div_zpow K₀ _ _ _ hπ, ← map_sub, isInteger_div_pow_iff K₀ ϖ₀ hπ hinj,
        ← Ideal.Quotient.eq, mk_rep]

  refine ⟨(blist K₀ ϖ₀ n).length - 1, fun j => ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).1,
    fun j => ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).2, ?_, ?_, h2, ?_, ?_, h5, h6⟩
  ·
    show ((blist K₀ ϖ₀ n)[0]'_).1 = 0
    simp only [ht, List.getElem_cons_zero]
  ·
    show ((blist K₀ ϖ₀ n)[0]'_).2 = 1 - (n : ℤ)
    simp only [ht, List.getElem_cons_zero]
  ·
    intro i j hij hlev hint
    dsimp only at hlev hint
    obtain ⟨e, he1, he2, q, hq⟩ := hmem i
    obtain ⟨e', -, -, q', hq'⟩ := hmem j
    have hne : (blist K₀ ϖ₀ n)[(i : ℕ)]'(hidx i) ≠ (blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j) := fun h =>
      hij (Fin.ext ((blist_nodup K₀ ϖ₀ n hπ hinj).getElem_inj_iff.1 h))
    rw [hq, hq'] at hne hlev hint
    simp only [entry] at hlev hint hne
    have hee : e = e' := by omega
    subst hee
    rw [sub_div_zpow K₀ _ _ _ hπ, ← map_sub, isInteger_div_pow_iff K₀ ϖ₀ hπ hinj, ← Ideal.Quotient.eq,
      mk_rep, mk_rep] at hint
    exact hne (by rw [hint])
  ·
    intro j
    by_cases hroot : ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).2 = 1 - (n : ℤ)
    · exact Or.inl hroot
    · right
      obtain ⟨hl1, hl2, hl3⟩ := h5 j
      obtain ⟨i, hi1, hi2⟩ := h6 ((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).1 (((blist K₀ ϖ₀ n)[(j : ℕ)]'(hidx j)).2 - 1)
        ⟨by omega, by omega, hl3⟩
      refine ⟨i, ?_, hi1, hi2⟩
      rcases lt_or_ge i j with h | h
      · exact h
      · have := h2 j i h; omega

end S_CerednikDrinfeld_Omega_exists_fin_ballEdges
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_fin_ballEdges (solution)
