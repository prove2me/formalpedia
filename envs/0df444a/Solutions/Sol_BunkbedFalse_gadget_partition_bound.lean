-- Prove2me | solution 1 for BunkbedFalse.gadget_partition_bound
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T19:00:27.431833+00:00
-- url     : https://prove2.me/submissions/70079ace-8928-476e-ac36-215d91eb48d0

import Definitions.Def_BunkbedPercolation
import Theorems.Thm_BunkbedFalse_gadget_conn
import Theorems.Thm_BunkbedFalse_gadget_conn_all
import Theorems.Thm_BunkbedFalse_gadget_sep
import Theorems.Thm_BunkbedAux_sum_weight_eq_one
import Theorems.Thm_BunkbedAux_partition_sum_eq_total
import Theorems.Thm_BunkbedAux_Pabc_add_Pab_c_eq_connProb

open Bunkbed Finset
open Fin.NatCast

namespace P54

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Weight basics (copied from the `gadget_conn` development) -/

private lemma weight_insert_notMem {E S : Finset (Sym2 V)} {e : Sym2 V}
    (hE : e ∉ E) (hS : S ⊆ E) (w : Sym2 V → ℚ) :
    weight (insert e E) w S = (1 - w e) * weight E w S := by
  have hes : e ∉ S := fun h => hE (hS h)
  have : insert e E \ S = insert e (E \ S) := by
    rw [Finset.insert_sdiff_of_notMem _ hes]
  rw [weight, weight, this, Finset.prod_insert (by simp [hE])]
  ring

private lemma weight_insert_mem {E S : Finset (Sym2 V)} {e : Sym2 V}
    (hE : e ∉ E) (hS : S ⊆ E) (w : Sym2 V → ℚ) :
    weight (insert e E) w (insert e S) = w e * weight E w S := by
  have hes : e ∉ S := fun h => hE (hS h)
  have h2 : insert e E \ insert e S = E \ S := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, by push_neg; exact ⟨fun h => hE (h ▸ h1), h2⟩⟩
  rw [weight, weight, h2, Finset.prod_insert hes]
  ring

private lemma sum_weight (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) :
    ∑ S ∈ E.powerset, weight E w S = 1 :=
  BunkbedAux.sum_weight_eq_one E w

/-! ### Reachability basics -/

open SimpleGraph in
private lemma reach_map {G H : SimpleGraph V} (φ : V → V)
    (hφ : ∀ u v : V, G.Adj u v → H.Adj (φ u) (φ v) ∨ φ u = φ v) {a b : V}
    (h : G.Reachable a b) : H.Reachable (φ a) (φ b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj q ih =>
      rcases hφ _ _ hadj with h1 | h1
      · exact h1.reachable.trans ih
      · rw [h1]; exact ih

private lemma adj_ofEdges {S : Finset (Sym2 V)} {u v : V} :
    (ofEdges S).Adj u v ↔ s(u, v) ∈ S ∧ u ≠ v := by
  simp [ofEdges, SimpleGraph.fromEdgeSet_adj]

private lemma not_reach_isolated {S : Finset (Sym2 V)} {a y : V} (hay : a ≠ y)
    (hiso : ∀ e ∈ S, y ∉ e) : ¬ (ofEdges S).Reachable a y := by
  intro h
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => exact hay rfl
  | cons hadj q =>
      rw [adj_ofEdges] at hadj
      exact hiso _ hadj.1 (by simp)

private lemma ofEdges_mono {S T : Finset (Sym2 V)} (h : S ⊆ T) :
    ofEdges S ≤ ofEdges T := by
  intro u v huv
  rw [adj_ofEdges] at huv ⊢
  exact ⟨h huv.1, huv.2⟩

private lemma reach_pendant {E S : Finset (Sym2 V)} {a x y : V}
    (hxy : x ≠ y) (hay : a ≠ y) (hiso : ∀ e ∈ E, y ∉ e) (hS : S ⊆ E) :
    (ofEdges (insert s(x, y) S)).Reachable a y ↔ (ofEdges S).Reachable a x := by
  have hisoS : ∀ e ∈ S, y ∉ e := fun e he => hiso e (hS he)
  constructor
  · intro h
    have hmap := reach_map (G := ofEdges (insert s(x, y) S)) (H := ofEdges S)
      (φ := fun v => if v = y then x else v) ?_ h
    · simpa [hay, hxy] using hmap
    · intro u v huv
      rw [adj_ofEdges, Finset.mem_insert] at huv
      obtain ⟨hmem, hne⟩ := huv
      rcases hmem with heq | hmem
      · right
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst hu; subst hv; simp [hxy]
        · subst hu; subst hv; simp [hxy]
      · left
        have hu : u ≠ y := fun h => hisoS _ hmem (by rw [h]; simp)
        have hv : v ≠ y := fun h => hisoS _ hmem (by rw [h]; simp)
        simp only [hu, hv, if_false]
        rw [adj_ofEdges]
        exact ⟨hmem, hne⟩
  · intro h
    have h1 : (ofEdges (insert s(x, y) S)).Reachable a x :=
      h.mono (ofEdges_mono (Finset.subset_insert _ _))
    have h2 : (ofEdges (insert s(x, y) S)).Adj x y := by
      rw [adj_ofEdges]
      exact ⟨Finset.mem_insert_self _ _, hxy⟩
    exact h1.trans h2.reachable

/-! ### The conditioning step -/

private lemma probOf_pendant (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a x y : V)
    (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y) (hiso : ∀ e ∈ E, y ∉ e) :
    probOf (insert s(a, y) (insert s(x, y) E)) w
        (fun S => (ofEdges S).Reachable a y)
      = w s(a, y) + (1 - w s(a, y)) * w s(x, y) *
          probOf E w (fun S => (ofEdges S).Reachable a x) := by
  have he2 : s(x, y) ∉ E := fun h => hiso _ h (by simp)
  have hne12 : s(a, y) ≠ s(x, y) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hax h1
    · exact hay h1
  have he1 : s(a, y) ∉ insert s(x, y) E := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne12, fun h => hiso _ h (by simp)⟩
  have hsubI : ∀ S : Finset (Sym2 V), S ⊆ E → insert s(x, y) S ⊆ insert s(x, y) E := by
    intro S hS
    exact Finset.insert_subset_insert _ hS
  have hA : ∑ S ∈ E.powerset, (if (ofEdges S).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w S else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro S hS
    rw [Finset.mem_powerset] at hS
    exact if_neg (not_reach_isolated hay (fun e he => hiso e (hS he)))
  have hB : ∑ S ∈ E.powerset, (if (ofEdges (insert s(x, y) S)).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(x, y) S) else 0)
      = (1 - w s(a, y)) * w s(x, y) *
          probOf E w (fun S => (ofEdges S).Reachable a x) := by
    rw [probOf, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hw : weight (insert s(a, y) (insert s(x, y) E)) w (insert s(x, y) S)
        = (1 - w s(a, y)) * (w s(x, y) * weight E w S) := by
      rw [weight_insert_notMem he1 (hsubI S hS) w, weight_insert_mem he2 hS w]
    by_cases hr : (ofEdges S).Reachable a x
    · rw [if_pos ((reach_pendant hxy hay hiso hS).2 hr), if_pos hr, hw]; ring
    · rw [if_neg (fun h => hr ((reach_pendant hxy hay hiso hS).1 h)), if_neg hr]; ring
  have hCD : ∀ S : Finset (Sym2 V), S ⊆ E →
      (ofEdges (insert s(a, y) S)).Reachable a y ∧
      (ofEdges (insert s(a, y) (insert s(x, y) S))).Reachable a y := by
    intro S _
    constructor
    · exact (show (ofEdges (insert s(a, y) S)).Adj a y by
        rw [adj_ofEdges]; exact ⟨Finset.mem_insert_self _ _, hay⟩).reachable
    · exact (show (ofEdges (insert s(a, y) (insert s(x, y) S))).Adj a y by
        rw [adj_ofEdges]; exact ⟨Finset.mem_insert_self _ _, hay⟩).reachable
  have hC : ∑ S ∈ E.powerset, (if (ofEdges (insert s(a, y) S)).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) S) else 0)
      = w s(a, y) * (1 - w s(x, y)) := by
    have : ∀ S ∈ E.powerset, (if (ofEdges (insert s(a, y) S)).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) S) else 0)
        = w s(a, y) * (1 - w s(x, y)) * weight E w S := by
      intro S hS
      rw [Finset.mem_powerset] at hS
      rw [if_pos (hCD S hS).1,
        weight_insert_mem he1 (hS.trans (Finset.subset_insert _ _)) w,
        weight_insert_notMem he2 hS w]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_weight, mul_one]
  have hD : ∑ S ∈ E.powerset, (if (ofEdges (insert s(a, y) (insert s(x, y) S))).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) (insert s(x, y) S)) else 0)
      = w s(a, y) * w s(x, y) := by
    have : ∀ S ∈ E.powerset,
        (if (ofEdges (insert s(a, y) (insert s(x, y) S))).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) (insert s(x, y) S)) else 0)
        = w s(a, y) * w s(x, y) * weight E w S := by
      intro S hS
      rw [Finset.mem_powerset] at hS
      rw [if_pos (hCD S hS).2, weight_insert_mem he1 (hsubI S hS) w,
        weight_insert_mem he2 hS w]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_weight, mul_one]
  rw [probOf, Finset.sum_powerset_insert he1, Finset.sum_powerset_insert he2,
    Finset.sum_powerset_insert he2, hA, hB, hC, hD]
  ring

/-! ### The gadget edge sets, peeled from the FAR end -/

/-- The spoke `a-v_j`. -/
private def spk (n j : ℕ) : Sym2 (Fin (n + 1)) := s((0 : Fin (n + 1)), ((j : ℕ) : Fin (n + 1)))

/-- The path edge `v_i-v_{i+1}`. -/
private def pth (n i : ℕ) : Sym2 (Fin (n + 1)) :=
  s(((i : ℕ) : Fin (n + 1)), ((i + 1 : ℕ) : Fin (n + 1)))

/-- The edges of the gadget `G_n` supported on `{0, k, k+1, ..., n}`. -/
private def Fk (n k : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  ((Finset.Ico k (n + 1)).image (spk n)) ∪ ((Finset.Ico k n).image (pth n))

private lemma Ico_insert (a b : ℕ) (h : a < b) :
    Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
  ext j
  simp only [Finset.mem_Ico, Finset.mem_insert]
  omega

private lemma cast_ne_cast {n a b : ℕ} (ha : a < n + 1) (hb : b < n + 1) (hab : a ≠ b) :
    ((a : ℕ) : Fin (n + 1)) ≠ ((b : ℕ) : Fin (n + 1)) := by
  intro h
  apply hab
  have := congrArg Fin.val h
  rwa [Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb] at this

private lemma cast_ne_zero' {n a : ℕ} (ha : a < n + 1) (ha0 : a ≠ 0) :
    ((a : ℕ) : Fin (n + 1)) ≠ 0 := by
  intro h
  apply ha0
  have := congrArg Fin.val h
  rwa [Fin.val_cast_of_lt ha, Fin.val_zero] at this

private lemma Fk_last (n : ℕ) : Fk n n = {spk n n} := by
  have h1 : Finset.Ico n (n + 1) = {n} := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  have h2 : Finset.Ico n n = (∅ : Finset ℕ) := by simp
  rw [Fk, h1, h2]
  simp

private lemma Fk_succ (n k : ℕ) (hk : k + 1 ≤ n) :
    Fk n k = insert (spk n k) (insert (pth n k) (Fk n (k + 1))) := by
  rw [Fk, Fk, Ico_insert k (n + 1) (by omega), Ico_insert k n (by omega),
    Finset.image_insert, Finset.image_insert, Finset.insert_union, Finset.union_insert]

/-- Every edge of `Fk n (k+1)` avoids the vertex `v_k`. -/
private lemma notMem_Fk (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ∀ e ∈ Fk n (k + 1), ((k : ℕ) : Fin (n + 1)) ∉ e := by
  intro e he
  simp only [Fk, Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at he
  rcases he with ⟨j, ⟨hj1, hj2⟩, rfl⟩ | ⟨i, ⟨hi1, hi2⟩, rfl⟩
  · rw [spk, Sym2.mem_iff]
    exact not_or.2 ⟨cast_ne_zero' (by omega) (by omega),
      cast_ne_cast (by omega) (by omega) (by omega)⟩
  · rw [pth, Sym2.mem_iff]
    exact not_or.2 ⟨cast_ne_cast (by omega) (by omega) (by omega),
      cast_ne_cast (by omega) (by omega) (by omega)⟩

private lemma gadgetE_eq (n : ℕ) : gadgetE n = Fk n 1 := by
  ext e
  simp only [gadgetE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨u, v⟩, hcond, rfl⟩
    rcases hcond with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · subst hu
      refine Finset.mem_union_left _ ?_
      rw [Finset.mem_image]
      refine ⟨v.val, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        refine ⟨?_, v.isLt⟩
        rcases Nat.eq_zero_or_pos v.val with h | h
        · exact absurd (Fin.val_eq_zero_iff.1 h) hv
        · exact h
      · rw [spk, Fin.cast_val_eq_self]
    · refine Finset.mem_union_right _ ?_
      rw [Finset.mem_image]
      refine ⟨u.val, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        have hvl : v.val < n + 1 := v.isLt
        have hu' : 1 ≤ u.val := hu
        have hv' : v.val = u.val + 1 := hv
        exact ⟨hu', by omega⟩
      · rw [pth, Fin.cast_val_eq_self]
        congr 1
        have hvl : v.val < n + 1 := v.isLt
        have hu' : 1 ≤ u.val := hu
        have hv' : v.val = u.val + 1 := hv
        have hh : (((u.val + 1 : ℕ)) : Fin (n + 1)).val = v.val := by
          rw [Fin.val_cast_of_lt (by omega)]; omega
        exact Fin.val_injective hh
  · intro he
    simp only [Fk, Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at he
    rcases he with ⟨j, ⟨hj1, hj2⟩, rfl⟩ | ⟨i, ⟨hi1, hi2⟩, rfl⟩
    · exact ⟨(0, ((j : ℕ) : Fin (n + 1))),
        Or.inl ⟨rfl, cast_ne_zero' (by omega) (by omega)⟩, rfl⟩
    · refine ⟨(((i : ℕ) : Fin (n + 1)), ((i + 1 : ℕ) : Fin (n + 1))), Or.inr ⟨?_, ?_⟩, rfl⟩
      · rw [Fin.val_cast_of_lt (by omega)]; omega
      · rw [Fin.val_cast_of_lt (by omega), Fin.val_cast_of_lt (by omega)]

/-! ### The downward recursion -/

private lemma probOf_Fk_last (n : ℕ) (P : ℚ) (hn : 1 ≤ n) :
    probOf (Fk n n) (gadgetW n P)
        (fun S => (ofEdges S).Reachable 0 ((n : ℕ) : Fin (n + 1))) = 1 - P := by
  have h1 : ((n : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
  have hw : gadgetW n P (spk n n) = 1 - P := by
    rw [gadgetW, spk]
    simp
  have hreach : (ofEdges ({spk n n} : Finset (Sym2 (Fin (n + 1))))).Reachable 0
      ((n : ℕ) : Fin (n + 1)) := by
    refine SimpleGraph.Adj.reachable ?_
    rw [adj_ofEdges]
    exact ⟨by simp [spk], Ne.symm h1⟩
  have hps : ({spk n n} : Finset (Sym2 (Fin (n + 1)))).powerset = {∅, {spk n n}} := by
    ext t
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  rw [probOf, Fk_last, hps, Finset.sum_insert (by simp),
    Finset.sum_singleton, if_neg (not_reach_isolated (Ne.symm h1) (by simp)), if_pos hreach]
  simp [weight, hw]

private lemma mainF (n : ℕ) (P : ℚ) (hn : 1 ≤ n) (hP : (1 : ℚ) + P ≠ 0) :
    ∀ d k : ℕ, 1 ≤ k → k + d = n →
      probOf (Fk n k) (gadgetW n P)
          (fun S => (ofEdges S).Reachable 0 ((k : ℕ) : Fin (n + 1)))
        = (1 - P ^ (2 * (d + 1))) / (1 + P) := by
  intro d
  induction d with
  | zero =>
    intro k hk1 hkn
    have hkeq : k = n := by omega
    subst hkeq
    rw [probOf_Fk_last k P hn]
    field_simp
    ring
  | succ d ih =>
    intro k hk1 hkn
    have hkn' : k + 1 ≤ n := by omega
    have hy : ((k : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
    have hx : ((k + 1 : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
    have hxy : ((k + 1 : ℕ) : Fin (n + 1)) ≠ ((k : ℕ) : Fin (n + 1)) :=
      cast_ne_cast (by omega) (by omega) (by omega)
    have hax : (0 : Fin (n + 1)) ≠ ((k + 1 : ℕ) : Fin (n + 1)) := Ne.symm hx
    have hay : (0 : Fin (n + 1)) ≠ ((k : ℕ) : Fin (n + 1)) := Ne.symm hy
    have hspk : spk n k = s((0 : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) := rfl
    have hpth : pth n k
        = s(((k + 1 : ℕ) : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) := by
      rw [pth]; exact Sym2.eq_swap
    have hw1 : gadgetW n P s((0 : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) = 1 - P := by
      rw [gadgetW]; simp
    have hw2 : gadgetW n P s(((k + 1 : ℕ) : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) = P := by
      have h0 : (0 : Fin (n + 1)) ∉
          s(((k + 1 : ℕ) : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) := by
        rw [Sym2.mem_iff]
        exact not_or.2 ⟨hax, hay⟩
      rw [gadgetW, if_neg h0]
    rw [Fk_succ n k hkn', hspk, hpth,
      probOf_pendant (Fk n (k + 1)) (gadgetW n P) 0 ((k + 1 : ℕ) : Fin (n + 1))
        ((k : ℕ) : Fin (n + 1)) hax hay hxy (notMem_Fk n k hk1 hkn'),
      ih (k + 1) (by omega) (by omega), hw1, hw2,
      show 2 * (d + 1 + 1) = 2 * (d + 1) + 2 from by ring, pow_add]
    field_simp
    ring

/-- The connection probability from the hub to the NEAR end `v₁` of the fan. -/
private lemma conn_near (n : ℕ) (P : ℚ) (hn : 1 ≤ n) (hP : (1 : ℚ) + P ≠ 0) :
    connProb (gadgetE n) (gadgetW n P) 0 1 = (1 - P ^ (2 * n)) / (1 + P) := by
  have h := mainF n P hn hP (n - 1) 1 le_rfl (by omega)
  rw [show n - 1 + 1 = n from by omega, Nat.cast_one] at h
  unfold connProb
  rw [gadgetE_eq n]
  exact h

/-! ### The general determinant identity -/

private lemma key_id (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a b c * Pa_b_c E w a b c - Pac_b E w a b c * Pab_c E w a b c
      = Pabc E w a b c - Pabc E w a b c * Pa_bc E w a b c
        - connProb E w a b * connProb E w a c := by
  have h1 := BunkbedAux.partition_sum_eq_total E w a b c
  rw [BunkbedAux.sum_weight_eq_one] at h1
  have h2 := BunkbedAux.Pabc_add_Pab_c_eq_connProb E w a b c
  have h3 := BunkbedAux.Pabc_add_Pab_c_eq_connProb E w a c b
  have h4 : Pabc E w a c b = Pabc E w a b c := by
    unfold Pabc probOf
    refine Finset.sum_congr rfl fun S _ => ?_
    have hiff : ((ofEdges S).Reachable a c ∧ (ofEdges S).Reachable c b)
        ↔ ((ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c) := by
      constructor
      · exact fun h => ⟨h.1.trans h.2, h.2.symm⟩
      · exact fun h => ⟨h.1.trans h.2, h.2.symm⟩
    by_cases h : (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun hc => h (hiff.1 hc)), if_neg h]
  have h5 : Pab_c E w a c b = Pac_b E w a b c := rfl
  rw [h4, h5] at h3
  linear_combination (Pabc E w a b c) * h1
    - (Pabc E w a b c + Pac_b E w a b c) * h2 - (connProb E w a b) * h3

/-! ### Elementary inequalities -/

private lemma geom_bound (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∀ k : ℕ, ((k : ℚ) + 1) * y ^ k * (1 - y) ≤ 1 - y ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hK : (0 : ℚ) ≤ (k : ℚ) + 1 := by positivity
    have hyk : y ^ (k + 1) ≤ y ^ k := by
      calc y ^ (k + 1) = y ^ k * y := by ring
        _ ≤ y ^ k * 1 := by
            exact mul_le_mul_of_nonneg_left hy1 (pow_nonneg hy0 k)
        _ = y ^ k := by ring
    have hmul : ((k : ℚ) + 1) * y ^ (k + 1) ≤ ((k : ℚ) + 1) * y ^ k :=
      mul_le_mul_of_nonneg_left hyk hK
    have h1 : ((k : ℚ) + 1) * y ^ (k + 1) * (1 - y)
        ≤ ((k : ℚ) + 1) * y ^ k * (1 - y) := by
      have hy' : (0 : ℚ) ≤ 1 - y := by linarith
      nlinarith [hmul, hy']
    have key : ((k : ℚ) + 1) * y ^ (k + 1) * (1 - y) ≤ 1 - y ^ (k + 1) :=
      le_trans h1 ih
    have h2 : y ^ (k + 1 + 1) = y ^ (k + 1) * y := by ring
    push_cast
    rw [h2]
    nlinarith [key]

private lemma arith (P q m A Q : ℚ) (hP0 : 0 < P) (hP1 : P < 1) (hq0 : 0 ≤ q)
    (hA : A = (1 - q * P ^ 2) / (1 + P) ^ 2 + m * (1 - P) * (q * P) / (1 + P))
    (hQ : Q = (1 - q * P ^ 2) / (1 + P))
    (hgb : m * q * (1 - P ^ 2) ≤ 1 - q * P ^ 2) :
    A - A * (q * P) - Q * Q ≥ (m * (1 - P) / (1 + P) - 1) * (q * P) := by
  have hden : (0 : ℚ) < 1 + P := by linarith
  have e : A - A * (q * P) - Q * Q - (m * (1 - P) / (1 + P) - 1) * (q * P)
      = q * P * (3 * P + P ^ 2 + P * (q * P) * (1 - P)
          - m * (1 - P ^ 2) * (q * P)) / (1 + P) ^ 2 := by
    subst hA
    subst hQ
    field_simp
    ring
  rw [ge_iff_le, ← sub_nonneg, e]
  refine div_nonneg ?_ (by positivity)
  have h1 : m * (1 - P ^ 2) * (q * P) ≤ P - q * P ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hgb hP0.le]
  have h2 : (0 : ℚ) ≤ 3 * P + P ^ 2 + P * (q * P) * (1 - P)
      - m * (1 - P ^ 2) * (q * P) := by
    nlinarith [mul_nonneg hq0 (sq_nonneg P), hP0, h1]
  exact mul_nonneg (mul_nonneg hq0 hP0.le) h2

end P54

theorem solution (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = P ^ (2 * n - 1) ∧
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pa_b_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) - Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      ≥ (n * (1 - P) / (1 + P) - 1) * P ^ (2 * n - 1) := by
  refine ⟨BunkbedFalse.gadget_sep n P hn hP0 hP1, ?_⟩
  have hPne : (1 : ℚ) + P ≠ 0 := by
    have : (0 : ℚ) < 1 + P := by linarith
    exact this.ne'
  have h2n : P ^ (2 * n) = P ^ (2 * n - 2) * P ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have h2n1 : P ^ (2 * n - 1) = P ^ (2 * n - 2) * P := by
    rw [← pow_succ]; congr 1; omega
  have hgb : (n : ℚ) * P ^ (2 * n - 2) * (1 - P ^ 2) ≤ 1 - P ^ (2 * n - 2) * P ^ 2 := by
    have h := P54.geom_bound (P ^ 2) (by positivity) (by nlinarith) (n - 1)
    rw [← pow_mul, ← pow_mul, show 2 * (n - 1) = 2 * n - 2 from by omega,
      show 2 * (n - 1 + 1) = 2 * n from by omega, h2n] at h
    have hc : (((n - 1 : ℕ) : ℚ) + 1) = (n : ℚ) := by
      rw [Nat.cast_sub (show 1 ≤ n by omega)]
      push_cast
      ring
    rw [hc] at h
    exact h
  rw [P54.key_id, BunkbedFalse.gadget_sep n P hn hP0 hP1,
    BunkbedFalse.gadget_conn_all n P hn hP0 hP1,
    BunkbedFalse.gadget_conn n P hn hP0 hP1,
    P54.conn_near n P (by omega) hPne, h2n, h2n1]
  exact P54.arith P (P ^ (2 * n - 2)) (n : ℚ) _ _ hP0 hP1 (by positivity) rfl rfl hgb
