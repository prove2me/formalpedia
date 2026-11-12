-- Prove2me | solution 1 for BunkbedFalse.hyperedge_simulation
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T19:00:34.162589+00:00
-- url     : https://prove2.me/submissions/cf6d57b7-0723-4486-ab13-091d0f643f20

import Definitions.Def_BunkbedPercolation
import Theorems.Thm_BunkbedFalse_gadget_conn
import Theorems.Thm_BunkbedFalse_gadget_conn_all
import Theorems.Thm_BunkbedFalse_gadget_sep
import Theorems.Thm_BunkbedAux_sum_weight_eq_one
import Theorems.Thm_BunkbedAux_partition_sum_eq_total
import Theorems.Thm_BunkbedAux_Pabc_add_Pab_c_eq_connProb

open Bunkbed Finset
open Fin.NatCast

namespace L41

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Weight basics (mirrors the pendant machinery of `gadget_conn`) -/

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

/-! ## Reachability basics -/

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

/-! ## The conditioning step at a pendant vertex -/

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

/-! ## The gadget edge sets, indexed from the far end -/

/-- The spoke `a-v_j`. -/
private def spk (n j : ℕ) : Sym2 (Fin (n + 1)) := s((0 : Fin (n + 1)), ((j : ℕ) : Fin (n + 1)))

/-- The path edge `v_i-v_{i+1}`. -/
private def pth (n i : ℕ) : Sym2 (Fin (n + 1)) :=
  s(((i : ℕ) : Fin (n + 1)), ((i + 1 : ℕ) : Fin (n + 1)))

/-- The edges of the gadget `G_n` supported on `{0} ∪ {k, k+1, ..., n}`. -/
private def Fk (n k : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  ((Finset.Ico k (n + 1)).image (spk n)) ∪ ((Finset.Ico k n).image (pth n))

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

private lemma Ico_insert_left (a b : ℕ) (h : a < b) :
    Finset.Ico a b = insert a (Finset.Ico (a + 1) b) := by
  ext j
  simp only [Finset.mem_Ico, Finset.mem_insert]
  omega

private lemma Fk_top (n : ℕ) : Fk n n = {spk n n} := by
  simp [Fk]

private lemma Fk_decomp (n k : ℕ) (h1 : 1 ≤ k) (h2 : k + 1 ≤ n) :
    Fk n k = insert (spk n k) (insert (pth n k) (Fk n (k + 1))) := by
  have e1 : Finset.Ico k (n + 1) = insert k (Finset.Ico (k + 1) (n + 1)) :=
    Ico_insert_left k (n + 1) (by omega)
  have e2 : Finset.Ico k n = insert k (Finset.Ico (k + 1) n) :=
    Ico_insert_left k n (by omega)
  simp only [Fk, e1, e2, Finset.image_insert, Finset.insert_union, Finset.union_insert]
  exact Finset.insert_comm _ _ _

/-- Every edge of `Fk n (k+1)` avoids the vertex `v_k`. -/
private lemma notMem_Fk (n k : ℕ) (h1 : 1 ≤ k) (h2 : k + 1 ≤ n) :
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

/-! ## The recursion from the far end -/

private lemma probOf_single (n j : ℕ) (P : ℚ) (h1 : 1 ≤ j) (h2 : j ≤ n) :
    probOf ({spk n j} : Finset (Sym2 (Fin (n + 1)))) (gadgetW n P)
        (fun S => (ofEdges S).Reachable 0 ((j : ℕ) : Fin (n + 1))) = 1 - P := by
  have hj : ((j : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
  have hw : gadgetW n P (spk n j) = 1 - P := by
    rw [gadgetW, spk]
    simp
  have hreach : (ofEdges ({spk n j} : Finset (Sym2 (Fin (n + 1))))).Reachable 0
      ((j : ℕ) : Fin (n + 1)) := by
    refine SimpleGraph.Adj.reachable ?_
    rw [adj_ofEdges]
    exact ⟨by simp [spk], Ne.symm hj⟩
  have hps : ({spk n j} : Finset (Sym2 (Fin (n + 1)))).powerset = {∅, {spk n j}} := by
    ext t
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  rw [probOf, hps, Finset.sum_insert (by simp),
    Finset.sum_singleton, if_neg (not_reach_isolated (Ne.symm hj) (by simp)), if_pos hreach]
  simp [weight, hw]

private lemma mainD (n : ℕ) (P : ℚ) (hn : 1 ≤ n) (hP : (1 : ℚ) + P ≠ 0) :
    ∀ d : ℕ, d + 1 ≤ n →
      probOf (Fk n (n - d)) (gadgetW n P)
          (fun S => (ofEdges S).Reachable 0 (((n - d : ℕ)) : Fin (n + 1)))
        = (1 - P ^ (2 * (d + 1))) / (1 + P) := by
  intro d
  induction d with
  | zero =>
      intro _
      simp only [Nat.sub_zero]
      rw [Fk_top, probOf_single n n P hn le_rfl]
      field_simp
      ring
  | succ d ih =>
      intro hd
      have hd' : d + 1 ≤ n := by omega
      have hk1 : 1 ≤ n - (d + 1) := by omega
      have hksucc : n - (d + 1) + 1 = n - d := by omega
      have hkn : n - (d + 1) + 1 ≤ n := by omega
      set k := n - (d + 1) with hk
      have hy : ((k : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
      have hx : ((k + 1 : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
      have hxy : ((k + 1 : ℕ) : Fin (n + 1)) ≠ ((k : ℕ) : Fin (n + 1)) :=
        cast_ne_cast (by omega) (by omega) (by omega)
      have hax : (0 : Fin (n + 1)) ≠ ((k + 1 : ℕ) : Fin (n + 1)) := Ne.symm hx
      have hay : (0 : Fin (n + 1)) ≠ ((k : ℕ) : Fin (n + 1)) := Ne.symm hy
      have hw1 : gadgetW n P s((0 : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) = 1 - P := by
        rw [gadgetW]
        simp
      have hw2 : gadgetW n P s(((k + 1 : ℕ) : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) = P := by
        have h0 : (0 : Fin (n + 1)) ∉
            s(((k + 1 : ℕ) : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) := by
          rw [Sym2.mem_iff]
          exact not_or.2 ⟨hax, hay⟩
        rw [gadgetW, if_neg h0]
      have hspk : spk n k = s((0 : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) := rfl
      have hpth : pth n k = s(((k + 1 : ℕ) : Fin (n + 1)), ((k : ℕ) : Fin (n + 1))) :=
        Sym2.eq_swap
      rw [Fk_decomp n k hk1 hkn, hspk, hpth,
        probOf_pendant (Fk n (k + 1)) (gadgetW n P) 0 ((k + 1 : ℕ) : Fin (n + 1))
          ((k : ℕ) : Fin (n + 1)) hax hay hxy (notMem_Fk n k hk1 hkn), hw1, hw2, hksucc,
        ih hd', show 2 * (d + 1 + 1) = 2 * (d + 1) + 2 from by ring, pow_add]
      field_simp
      ring

private lemma conn_one (n : ℕ) (P : ℚ) (hn : 1 ≤ n) (hP : (1 : ℚ) + P ≠ 0) :
    connProb (gadgetE n) (gadgetW n P) 0 1 = (1 - P ^ (2 * n)) / (1 + P) := by
  have h := mainD n P hn hP (n - 1) (by omega)
  rw [show n - (n - 1) = 1 from by omega, show 2 * (n - 1 + 1) = 2 * n from by omega,
    Nat.cast_one] at h
  unfold connProb
  rw [gadgetE_eq n]
  exact h

/-! ## Generalities on `probOf` and the algebraic identity -/

private lemma probOf_congr (E : Finset (Sym2 V)) (w : Sym2 V → ℚ)
    (ev1 ev2 : Finset (Sym2 V) → Prop) [DecidablePred ev1] [DecidablePred ev2]
    (h : ∀ S, ev1 S ↔ ev2 S) : probOf E w ev1 = probOf E w ev2 := by
  unfold probOf
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h1 : ev1 S
  · rw [if_pos h1, if_pos ((h S).1 h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 ((h S).2 hc))]

private lemma pabc_swap (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a c b = Pabc E w a b c := by
  unfold Pabc
  refine probOf_congr E w _ _ ?_
  intro S
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.trans h2, h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.trans h2, h2.symm⟩

private lemma pab_c_swap (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    Pab_c E w a c b = Pac_b E w a b c := by
  unfold Pab_c Pac_b
  exact probOf_congr E w _ _ (fun _ => Iff.rfl)

private lemma algid (A B C D F Q₁ Q₂ : ℚ) (hm : A + B + C + D + F = 1)
    (h1 : A + B = Q₁) (h2 : A + C = Q₂) :
    A * F - B * C = A - A * D - Q₁ * Q₂ := by
  linear_combination A * hm - (A + C) * h1 - Q₁ * h2

/-! ## The two analytic ingredients -/

private lemma pow_bound (k : ℕ) (x : ℚ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ((k : ℚ) + 1) * x ^ k * (1 - x) ≤ 1 - x ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hXnn : (0 : ℚ) ≤ x ^ k := by positivity
      have hX1 : x ^ k ≤ 1 := pow_le_one₀ h0 h1
      have e1 : x ^ (k + 1) = x ^ k * x := pow_succ x k
      have e2 : x ^ (k + 1 + 1) = x ^ k * x * x := by rw [pow_succ, pow_succ]
      rw [e1] at ih
      rw [e1, e2]
      have hint1 : x * (((k : ℚ) + 1) * x ^ k * (1 - x)) ≤ x * (1 - x ^ k * x) :=
        mul_le_mul_of_nonneg_left ih h0
      have hint3 : (0 : ℚ) ≤ (1 - x) * (1 - x ^ k * x) := by
        refine mul_nonneg (by linarith) ?_
        nlinarith
      push_cast
      nlinarith [hint1, hint3]

private lemma final_ineq (N P G A D Q : ℚ) (hP0 : 0 < P) (hP1 : P < 1) (hG0 : 0 < G)
    (hb : N * (1 - P ^ 2) * G ≤ 1 - P ^ 2 * G)
    (hA : A = (1 - P ^ 2 * G) / (1 + P) ^ 2 + N * (1 - P) * (P * G) / (1 + P))
    (hD : D = P * G)
    (hQ : Q = (1 - P ^ 2 * G) / (1 + P)) :
    A - A * D - Q * Q > (N * (1 - P) / (1 + P) - 1) * D := by
  have hu : (0 : ℚ) < 1 + P := by linarith
  have hne : (1 : ℚ) + P ≠ 0 := ne_of_gt hu
  subst hA
  subst hD
  subst hQ
  rw [gt_iff_lt, ← sub_pos]
  have key : (1 - P ^ 2 * G) / (1 + P) ^ 2 + N * (1 - P) * (P * G) / (1 + P)
      - ((1 - P ^ 2 * G) / (1 + P) ^ 2 + N * (1 - P) * (P * G) / (1 + P)) * (P * G)
      - (1 - P ^ 2 * G) / (1 + P) * ((1 - P ^ 2 * G) / (1 + P))
      - (N * (1 - P) / (1 + P) - 1) * (P * G)
      = (N * P ^ 4 * G ^ 2 - N * P ^ 2 * G ^ 2 - P ^ 4 * G ^ 2 + P ^ 3 * G ^ 2
          + P ^ 3 * G + 3 * P ^ 2 * G) / (1 + P) ^ 2 := by
    field_simp
    ring
  rw [key]
  refine div_pos ?_ (by positivity)
  have h1 : N * (1 - P ^ 2) * G * (P ^ 2 * G) ≤ (1 - P ^ 2 * G) * (P ^ 2 * G) :=
    mul_le_mul_of_nonneg_right hb (by positivity)
  nlinarith [h1, mul_pos (mul_pos hP0 hP0) hG0, mul_pos (mul_pos (mul_pos hP0 hP0) hP0) hG0,
    mul_pos (mul_pos (mul_pos hP0 hP0) hP0) (mul_pos hG0 hG0)]

end L41

theorem solution (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) ∧
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pa_b_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) - Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      > (n * (1 - P) / (1 + P) - 1) * Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) := by
  have hu0 : (0 : ℚ) < 1 + P := by linarith
  have hune : (1 : ℚ) + P ≠ 0 := ne_of_gt hu0
  -- the two connection probabilities
  have hQ1 : connProb (gadgetE n) (gadgetW n P) 0 1 = (1 - P ^ (2 * n)) / (1 + P) :=
    L41.conn_one n P (by omega) hune
  have hQ2 : connProb (gadgetE n) (gadgetW n P) 0 (Fin.last n) = (1 - P ^ (2 * n)) / (1 + P) :=
    BunkbedFalse.gadget_conn n P hn hP0 hP1
  have hs1 := BunkbedAux.Pabc_add_Pab_c_eq_connProb (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
  have hs2 : Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      + Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      = connProb (gadgetE n) (gadgetW n P) 0 (Fin.last n) := by
    have h := BunkbedAux.Pabc_add_Pab_c_eq_connProb (gadgetE n) (gadgetW n P) 0 (Fin.last n) 1
    rwa [L41.pabc_swap, L41.pab_c_swap] at h
  have hmass : Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      + Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      + Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      + Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      + Pa_b_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = 1 := by
    rw [BunkbedAux.partition_sum_eq_total, BunkbedAux.sum_weight_eq_one]
  refine ⟨by rw [hQ1] at hs1; rw [hQ2] at hs2; linarith, ?_⟩
  -- the determinant identity
  have hid := L41.algid (Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n))
    (Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n))
    (Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n))
    (Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n))
    (Pa_b_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n))
    (connProb (gadgetE n) (gadgetW n P) 0 1)
    (connProb (gadgetE n) (gadgetW n P) 0 (Fin.last n)) hmass hs1 hs2
  rw [hid, hQ1, hQ2]
  -- now a strict rational inequality
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hA : Pabc (gadgetE (m + 1)) (gadgetW (m + 1) P) 0 1 (Fin.last (m + 1))
      = (1 - P ^ 2 * P ^ (2 * m)) / (1 + P) ^ 2
        + ((m : ℚ) + 1) * (1 - P) * (P * P ^ (2 * m)) / (1 + P) := by
    rw [BunkbedFalse.gadget_conn_all (m + 1) P hn hP0 hP1,
      show 2 * (m + 1) - 1 = 2 * m + 1 from by omega,
      show 2 * (m + 1) = 2 * m + 2 from by ring]
    push_cast
    ring
  have hD : Pa_bc (gadgetE (m + 1)) (gadgetW (m + 1) P) 0 1 (Fin.last (m + 1))
      = P * P ^ (2 * m) := by
    rw [BunkbedFalse.gadget_sep (m + 1) P hn hP0 hP1,
      show 2 * (m + 1) - 1 = 2 * m + 1 from by omega]
    ring
  have hQ : (1 - P ^ (2 * (m + 1))) / (1 + P) = (1 - P ^ 2 * P ^ (2 * m)) / (1 + P) := by
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring]
    ring
  have hb : ((m : ℚ) + 1) * (1 - P ^ 2) * P ^ (2 * m) ≤ 1 - P ^ 2 * P ^ (2 * m) := by
    have h := L41.pow_bound m (P ^ 2) (by positivity) (by nlinarith)
    rw [← pow_mul, ← pow_mul, show 2 * (m + 1) = 2 * m + 2 from by ring] at h
    have h2 : (P : ℚ) ^ (2 * m + 2) = P ^ 2 * P ^ (2 * m) := by ring
    rw [h2] at h
    linarith
  push_cast
  exact L41.final_ineq ((m : ℚ) + 1) P (P ^ (2 * m)) _ _ _ hP0 hP1 (by positivity) hb hA hD hQ
