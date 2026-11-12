-- Prove2me | solution 1 for BunkbedFalse.gadget_conn_all
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T18:30:28.953293+00:00
-- url     : https://prove2.me/submissions/fdc77f68-8b56-4bc2-888d-eedd2f3104b0

import Definitions.Def_BunkbedPercolation

open Bunkbed Finset
open Fin.NatCast

/-! ## Part 0: the cylinder-event probability -/

private lemma cyl {V : Type*} [Fintype V] [DecidableEq V]
    (E O C : Finset (Sym2 V)) (w : Sym2 V → ℚ)
    (hO : O ⊆ E) (hC : C ⊆ E) (hd : Disjoint O C) :
    ∑ S ∈ E.powerset, (if O ⊆ S ∧ Disjoint S C then weight E w S else 0)
      = (∏ e ∈ O, w e) * ∏ e ∈ C, (1 - w e) := by
  classical
  set F : Finset (Sym2 V) := E \ (O ∪ C) with hF
  have key : ∑ S ∈ E.powerset, (if O ⊆ S ∧ Disjoint S C then weight E w S else 0)
      = ∑ T ∈ F.powerset, weight E w (O ∪ T) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (i := fun S => S \ O) (j := fun T => O ∪ T) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      simp only [Finset.mem_powerset, hF]
      intro e he
      simp only [Finset.mem_sdiff] at he ⊢
      refine ⟨hS.1 he.1, ?_⟩
      simp only [Finset.mem_union, not_or]
      refine ⟨he.2, ?_⟩
      exact fun hc => (Finset.disjoint_right.mp hS.2.2 hc) he.1
    · intro T hT
      simp only [Finset.mem_powerset, hF] at hT
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, Finset.subset_union_left, ?_⟩
      · exact Finset.union_subset hO (fun e he => (Finset.mem_sdiff.mp (hT he)).1)
      · rw [Finset.disjoint_union_left]
        refine ⟨hd, ?_⟩
        rw [Finset.disjoint_left]
        intro e he hc
        have := hT he
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at this
        exact this.2.2 hc
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.union_sdiff_of_subset hS.2.1
    · intro T hT
      simp only [Finset.mem_powerset, hF] at hT
      rw [Finset.union_sdiff_left]
      apply Finset.sdiff_eq_self_of_disjoint
      rw [Finset.disjoint_left]
      intro e he hc
      have := hT he
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at this
      exact this.2.1 hc
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      rw [Finset.union_sdiff_of_subset hS.2.1]
  rw [key]
  have hsplit : ∀ T ∈ F.powerset, weight E w (O ∪ T)
      = ((∏ e ∈ O, w e) * ∏ e ∈ C, (1 - w e)) * ((∏ e ∈ T, w e) * ∏ e ∈ F \ T, (1 - w e)) := by
    intro T hT
    simp only [Finset.mem_powerset, hF] at hT
    have hdOT : Disjoint O T := by
      rw [Finset.disjoint_right]
      intro e he hO'
      have := hT he
      simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at this
      exact this.2.1 hO'
    have h1 : ∏ e ∈ O ∪ T, w e = (∏ e ∈ O, w e) * ∏ e ∈ T, w e :=
      Finset.prod_union hdOT
    have h2 : E \ (O ∪ T) = C ∪ (F \ T) := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union, hF, not_or]
      constructor
      · rintro ⟨heE, hnO, hnT⟩
        by_cases hc : e ∈ C
        · exact Or.inl hc
        · exact Or.inr ⟨⟨heE, hnO, hc⟩, hnT⟩
      · rintro (hc | ⟨⟨heE, hnO, hnC⟩, hnT⟩)
        · refine ⟨hC hc, ?_, ?_⟩
          · exact fun hO' => (Finset.disjoint_left.mp hd hO') hc
          · intro hT'
            have := hT hT'
            simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at this
            exact this.2.2 hc
        · exact ⟨heE, hnO, hnT⟩
    have hdCF : Disjoint C (F \ T) := by
      rw [Finset.disjoint_left]
      intro e he hc
      simp only [Finset.mem_sdiff, hF, Finset.mem_union, not_or] at hc
      exact hc.1.2.2 he
    simp only [weight, h1, h2, Finset.prod_union hdCF]
    ring
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  have : ∑ T ∈ F.powerset, (∏ e ∈ T, w e) * ∏ e ∈ F \ T, (1 - w e)
      = ∏ e ∈ F, (w e + (1 - w e)) := (Finset.prod_add _ _ _).symm
  rw [this]
  simp

private lemma total {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) :
    ∑ S ∈ E.powerset, weight E w S = 1 := by
  have : ∑ S ∈ E.powerset, weight E w S = ∏ e ∈ E, (w e + (1 - w e)) :=
    (Finset.prod_add _ _ _).symm
  rw [this]; simp

/-! ## Part 1: edges of the gadget -/

private def sp (n i : ℕ) : Sym2 (Fin (n + 1)) := s((0 : Fin (n + 1)), ((i : ℕ) : Fin (n + 1)))

private def pe (n i : ℕ) : Sym2 (Fin (n + 1)) :=
  s(((i : ℕ) : Fin (n + 1)), ((i + 1 : ℕ) : Fin (n + 1)))

private lemma vc {n i : ℕ} (h : i ≤ n) : (((i : ℕ) : Fin (n + 1)) : ℕ) = i := by
  rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]

private lemma vc_ne_zero {n i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) :
    ((i : ℕ) : Fin (n + 1)) ≠ 0 := by
  intro h
  have h0 : (((i : ℕ) : Fin (n + 1)) : ℕ) = 0 := by rw [h]; rfl
  rw [vc h2] at h0
  omega

private lemma mem_gadgetE {n : ℕ} {e : Sym2 (Fin (n + 1))} :
    e ∈ gadgetE n ↔ ∃ x y : Fin (n + 1),
      ((x = 0 ∧ y ≠ 0) ∨ (1 ≤ (x : ℕ) ∧ (y : ℕ) = (x : ℕ) + 1)) ∧ e = s(x, y) := by
  simp only [gadgetE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨x, y, h, rfl⟩; exact ⟨x, y, h, rfl⟩
  · rintro ⟨x, y, h, rfl⟩; exact ⟨x, y, h, rfl⟩

private lemma sp_mem {n i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) : sp n i ∈ gadgetE n := by
  rw [mem_gadgetE]
  exact ⟨0, ((i : ℕ) : Fin (n + 1)), Or.inl ⟨rfl, vc_ne_zero h1 h2⟩, rfl⟩

private lemma pe_mem {n i : ℕ} (h1 : 1 ≤ i) (h2 : i + 1 ≤ n) : pe n i ∈ gadgetE n := by
  rw [mem_gadgetE]
  refine ⟨((i : ℕ) : Fin (n + 1)), ((i + 1 : ℕ) : Fin (n + 1)), Or.inr ⟨?_, ?_⟩, rfl⟩
  · rw [vc (by omega)]; omega
  · rw [vc (by omega), vc (by omega)]

private lemma zero_notMem_pe {n i : ℕ} (h1 : 1 ≤ i) (h2 : i + 1 ≤ n) :
    (0 : Fin (n + 1)) ∉ pe n i := by
  simp only [pe, Sym2.mem_iff]
  push_neg
  exact ⟨fun h => vc_ne_zero h1 (by omega) h.symm, fun h => vc_ne_zero (by omega) h2 h.symm⟩

private lemma w_sp {n i : ℕ} (P : ℚ) : gadgetW n P (sp n i) = 1 - P := by
  simp [gadgetW, sp, Sym2.mem_iff]

private lemma w_pe {n i : ℕ} (P : ℚ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ n) :
    gadgetW n P (pe n i) = P := by
  rw [gadgetW]
  rw [if_neg (zero_notMem_pe h1 h2)]

private lemma sp_inj {n i j : ℕ} (hi : 1 ≤ i) (hi' : i ≤ n) (hj' : j ≤ n)
    (h : sp n i = sp n j) : i = j := by
  simp only [sp, Sym2.eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨h1, h2⟩
  · have := congrArg (fun z : Fin (n + 1) => (z : ℕ)) h
    simpa [vc hi', vc hj'] using this
  · exfalso
    have := congrArg (fun z : Fin (n + 1) => (z : ℕ)) h2
    simp only [vc hi'] at this
    simp at this
    omega

private lemma pe_inj {n i j : ℕ} (hi : 1 ≤ i) (hi' : i + 1 ≤ n) (hj : 1 ≤ j) (hj' : j + 1 ≤ n)
    (h : pe n i = pe n j) : i = j := by
  simp only [pe, Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · have := congrArg (fun z : Fin (n + 1) => (z : ℕ)) h1
    simpa [vc (show i ≤ n by omega), vc (show j ≤ n by omega)] using this
  · exfalso
    have e1 := congrArg (fun z : Fin (n + 1) => (z : ℕ)) h1
    have e2 := congrArg (fun z : Fin (n + 1) => (z : ℕ)) h2
    simp only [vc (show i ≤ n by omega), vc (show j + 1 ≤ n by omega),
      vc (show j ≤ n by omega), vc (show i + 1 ≤ n by omega)] at e1 e2
    omega

private lemma pe_ne_sp {n i j : ℕ} (hi : 1 ≤ i) (hi' : i + 1 ≤ n) : pe n i ≠ sp n j := by
  intro h
  have : (0 : Fin (n + 1)) ∈ pe n i := by rw [h]; simp [sp, Sym2.mem_iff]
  exact zero_notMem_pe hi hi' this

private lemma pe_zero {n : ℕ} : pe n 0 = sp n 1 := by
  simp [pe, sp]

private lemma pe_top {n : ℕ} : pe n n = sp n n := by
  have h : ((n + 1 : ℕ) : Fin (n + 1)) = 0 := by
    apply Fin.ext
    rw [Fin.val_natCast]
    simp
  simp only [pe, sp, h]
  rw [Sym2.eq_swap]

/-! ## Part 2: blocks and disconnection -/

private lemma reach_invariant {V : Type*} {G : SimpleGraph V} {W : Set V}
    (hW : ∀ x y, G.Adj x y → x ∈ W → y ∈ W) :
    ∀ {u v : V}, G.Walk u v → u ∈ W → v ∈ W := by
  intro u v p
  induction p with
  | nil => intro h; exact h
  | cons hadj q ih => intro h; exact ih (hW _ _ hadj h)

private def Op (n lo hi : ℕ) : Finset (Sym2 (Fin (n + 1))) := (Finset.Ico lo hi).image (pe n)

private def Cl (n lo hi : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  (Finset.Icc lo hi).image (sp n) ∪ {pe n (lo - 1), pe n hi}

private abbrev Blk (n lo hi : ℕ) (S : Finset (Sym2 (Fin (n + 1)))) : Prop :=
  Op n lo hi ⊆ S ∧ Disjoint S (Cl n lo hi)

private lemma sp_mem_Cl {n lo hi i : ℕ} (h1 : lo ≤ i) (h2 : i ≤ hi) :
    sp n i ∈ Cl n lo hi := by
  simp only [Cl, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  exact Or.inl ⟨i, ⟨h1, h2⟩, rfl⟩

private lemma pe_lo_mem_Cl {n lo hi : ℕ} : pe n (lo - 1) ∈ Cl n lo hi := by
  simp [Cl]

private lemma pe_hi_mem_Cl {n lo hi : ℕ} : pe n hi ∈ Cl n lo hi := by
  simp [Cl]

private lemma Blk_sp {n lo hi i : ℕ} {S : Finset (Sym2 (Fin (n + 1)))} (hB : Blk n lo hi S)
    (h1 : lo ≤ i) (h2 : i ≤ hi) : sp n i ∉ S :=
  Finset.disjoint_right.mp hB.2 (sp_mem_Cl h1 h2)

private lemma Blk_pe_lo {n lo hi : ℕ} {S : Finset (Sym2 (Fin (n + 1)))} (hB : Blk n lo hi S) :
    pe n (lo - 1) ∉ S :=
  Finset.disjoint_right.mp hB.2 pe_lo_mem_Cl

private lemma Blk_pe_hi {n lo hi : ℕ} {S : Finset (Sym2 (Fin (n + 1)))} (hB : Blk n lo hi S) :
    pe n hi ∉ S :=
  Finset.disjoint_right.mp hB.2 pe_hi_mem_Cl

private lemma Blk_pe {n lo hi i : ℕ} {S : Finset (Sym2 (Fin (n + 1)))} (hB : Blk n lo hi S)
    (h1 : lo ≤ i) (h2 : i < hi) : pe n i ∈ S :=
  hB.1 (Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨h1, h2⟩, rfl⟩)

private lemma self_cast {n : ℕ} (x : Fin (n + 1)) : (((x : ℕ) : ℕ) : Fin (n + 1)) = x := by
  simp

private lemma edge_eq {n : ℕ} (x y : Fin (n + 1)) (i j : ℕ) (hi : (x : ℕ) = i)
    (hj : (y : ℕ) = j) : s(x, y) = s(((i : ℕ) : Fin (n + 1)), ((j : ℕ) : Fin (n + 1))) := by
  rw [← hi, ← hj, self_cast, self_cast]

private lemma not_reach {n lo hi v : ℕ} {S : Finset (Sym2 (Fin (n + 1)))}
    (hS : S ⊆ gadgetE n) (h1 : 1 ≤ lo) (h3 : hi ≤ n)
    (hB : Blk n lo hi S) (hv1 : lo ≤ v) (hv2 : v ≤ hi) :
    ¬ (ofEdges S).Reachable 0 ((v : ℕ) : Fin (n + 1)) := by
  intro hR
  set W : Set (Fin (n + 1)) := {x | lo ≤ (x : ℕ) ∧ (x : ℕ) ≤ hi} with hWdef
  have hinv : ∀ x y, (ofEdges S).Adj x y → x ∈ W → y ∈ W := by
    intro x y hadj hx
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨hmem, hne⟩ := hadj
    rw [Finset.mem_coe] at hmem
    have hxW : lo ≤ (x : ℕ) ∧ (x : ℕ) ≤ hi := hx
    obtain ⟨a, b, hcond, heq⟩ := mem_gadgetE.mp (hS hmem)
    rw [Sym2.eq_iff] at heq
    have hxn : (x : ℕ) ≤ n := by have := x.isLt; omega
    have hyn : (y : ℕ) ≤ n := by have := y.isLt; omega
    have hcv : ((a : ℕ) = 0 ∧ 1 ≤ (b : ℕ)) ∨ (1 ≤ (a : ℕ) ∧ (b : ℕ) = (a : ℕ) + 1) := by
      rcases hcond with ⟨hz, hnz⟩ | hh
      · refine Or.inl ⟨by rw [hz]; rfl, ?_⟩
        rcases Nat.eq_zero_or_pos (b : ℕ) with hb | hb
        · exact absurd (Fin.ext (by simp [hb])) hnz
        · exact hb
      · exact Or.inr hh
    have heqv : ((x : ℕ) = (a : ℕ) ∧ (y : ℕ) = (b : ℕ)) ∨
        ((x : ℕ) = (b : ℕ) ∧ (y : ℕ) = (a : ℕ)) := by
      rcases heq with ⟨e, e'⟩ | ⟨e, e'⟩
      · exact Or.inl ⟨by rw [e], by rw [e']⟩
      · exact Or.inr ⟨by rw [e], by rw [e']⟩
    have hcases : ((x : ℕ) = 0 ∧ 1 ≤ (y : ℕ)) ∨ ((y : ℕ) = 0 ∧ 1 ≤ (x : ℕ)) ∨
        (1 ≤ (x : ℕ) ∧ (y : ℕ) = (x : ℕ) + 1) ∨ (1 ≤ (y : ℕ) ∧ (x : ℕ) = (y : ℕ) + 1) := by
      rcases heqv with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hcv with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> omega
    rcases hcases with ⟨hx0, _⟩ | ⟨hy0, hx1⟩ | ⟨hx1, hy1⟩ | ⟨hy1, hx1⟩
    · exact absurd hxW.1 (by omega)
    · exfalso
      have hey : y = 0 := Fin.ext (by simp [hy0])
      have : s(x, y) = sp n (x : ℕ) := by
        rw [edge_eq x y (x : ℕ) 0 rfl hy0, sp, Nat.cast_zero]
        exact Sym2.eq_swap
      rw [this] at hmem
      exact Blk_sp hB hxW.1 hxW.2 hmem
    · by_cases hxhi : (x : ℕ) = hi
      · exfalso
        have : s(x, y) = pe n hi := by
          rw [pe]
          exact edge_eq x y hi (hi + 1) hxhi (by omega)
        rw [this] at hmem
        exact Blk_pe_hi hB hmem
      · exact ⟨by omega, by omega⟩
    · by_cases hxlo : (x : ℕ) = lo
      · exfalso
        have hlo : lo - 1 + 1 = lo := by omega
        have : s(x, y) = pe n (lo - 1) := by
          rw [pe, hlo, edge_eq x y lo (lo - 1) hxlo (by omega)]
          exact Sym2.eq_swap
        rw [this] at hmem
        exact Blk_pe_lo hB hmem
      · exact ⟨by omega, by omega⟩
  have h0 : (0 : Fin (n + 1)) ∈ W := by
    obtain ⟨p⟩ := hR.symm
    refine reach_invariant hinv p ?_
    refine ⟨?_, ?_⟩
    · rw [vc (by omega : v ≤ n)]; exact hv1
    · rw [vc (by omega : v ≤ n)]; exact hv2
  have hz : lo ≤ ((0 : Fin (n + 1)) : ℕ) := h0.1
  simp at hz
  omega

/-! ## Part 3: existence and uniqueness of the block -/

private lemma reach_pe {n : ℕ} {S : Finset (Sym2 (Fin (n + 1)))} {a : ℕ} (ha : 1 ≤ a) :
    ∀ b : ℕ, a ≤ b → b ≤ n → (∀ i ∈ Finset.Ico a b, pe n i ∈ S) →
      (ofEdges S).Reachable ((a : ℕ) : Fin (n + 1)) ((b : ℕ) : Fin (n + 1)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _ _; exact SimpleGraph.Reachable.refl _
  | succ b hb ih =>
    intro hbn hall
    have h1 : (ofEdges S).Reachable ((a : ℕ) : Fin (n + 1)) ((b : ℕ) : Fin (n + 1)) :=
      ih (by omega) (fun i hi => hall i (Finset.mem_Ico.mpr
        ⟨(Finset.mem_Ico.mp hi).1, by have := (Finset.mem_Ico.mp hi).2; omega⟩))
    have hadj : (ofEdges S).Adj ((b : ℕ) : Fin (n + 1)) ((b + 1 : ℕ) : Fin (n + 1)) := by
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨Finset.mem_coe.mpr (hall b (Finset.mem_Ico.mpr ⟨hb, by omega⟩)), ?_⟩
      intro hcon
      have := congrArg (fun z : Fin (n + 1) => (z : ℕ)) hcon
      simp only [vc (show b ≤ n by omega), vc (show b + 1 ≤ n by omega)] at this
      omega
    exact h1.trans hadj.reachable

private lemma exists_blk {n : ℕ} {S : Finset (Sym2 (Fin (n + 1)))} (hS : S ⊆ gadgetE n)
    {v : ℕ} (hv1 : 1 ≤ v) (hv2 : v ≤ n)
    (h : ¬ (ofEdges S).Reachable 0 ((v : ℕ) : Fin (n + 1))) :
    ∃ lo hi, 1 ≤ lo ∧ lo ≤ v ∧ v ≤ hi ∧ hi ≤ n ∧ Blk n lo hi S := by
  classical
  set T : Finset ℕ := (Finset.Icc v n).filter (fun b => ∀ i ∈ Finset.Ico v b, pe n i ∈ S)
    with hTdef
  set L : Finset ℕ := (Finset.Icc 1 v).filter (fun a => ∀ i ∈ Finset.Ico a v, pe n i ∈ S)
    with hLdef
  have hvT : v ∈ T := by
    simp only [hTdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hv2⟩, by simp⟩
  have hvL : v ∈ L := by
    simp only [hLdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hv1, le_rfl⟩, by simp⟩
  set hi : ℕ := T.max' ⟨v, hvT⟩ with hhidef
  set lo : ℕ := L.min' ⟨v, hvL⟩ with hlodef
  have hhiT : hi ∈ T := Finset.max'_mem T ⟨v, hvT⟩
  have hloL : lo ∈ L := Finset.min'_mem L ⟨v, hvL⟩
  rw [hTdef, Finset.mem_filter, Finset.mem_Icc] at hhiT
  rw [hLdef, Finset.mem_filter, Finset.mem_Icc] at hloL
  have hvhi : v ≤ hi := hhiT.1.1
  have hhin : hi ≤ n := hhiT.1.2
  have hlo1 : 1 ≤ lo := hloL.1.1
  have hlov : lo ≤ v := hloL.1.2
  have hopen : ∀ i, lo ≤ i → i < hi → pe n i ∈ S := by
    intro i ha hb
    by_cases hiv : i < v
    · exact hloL.2 i (Finset.mem_Ico.mpr ⟨ha, hiv⟩)
    · exact hhiT.2 i (Finset.mem_Ico.mpr ⟨by omega, hb⟩)
  have hreach : ∀ i, lo ≤ i → i ≤ hi →
      (ofEdges S).Reachable ((i : ℕ) : Fin (n + 1)) ((v : ℕ) : Fin (n + 1)) := by
    intro i ha hb
    by_cases hiv : i ≤ v
    · exact reach_pe (show 1 ≤ i by omega) v hiv hv2
        (fun j hj => hloL.2 j (Finset.mem_Ico.mpr
          ⟨by have := (Finset.mem_Ico.mp hj).1; omega, (Finset.mem_Ico.mp hj).2⟩))
    · exact (reach_pe hv1 i (by omega) (by omega)
        (fun j hj => hhiT.2 j (Finset.mem_Ico.mpr
          ⟨(Finset.mem_Ico.mp hj).1, by have := (Finset.mem_Ico.mp hj).2; omega⟩))).symm
  have hspoke : ∀ i, lo ≤ i → i ≤ hi → sp n i ∉ S := by
    intro i ha hb hin
    apply h
    have hadj : (ofEdges S).Adj 0 ((i : ℕ) : Fin (n + 1)) := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr hin,
        fun hcon => vc_ne_zero (show 1 ≤ i by omega) (show i ≤ n by omega) hcon.symm⟩
    exact hadj.reachable.trans (hreach i ha hb)
  have hpehi : pe n hi ∉ S := by
    by_cases hn : hi = n
    · rw [hn, pe_top]
      exact hspoke n (by omega) (by omega)
    · intro hin
      have hmem : hi + 1 ∈ T := by
        simp only [hTdef, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        intro i hi'
        rcases Nat.lt_or_ge i hi with hlt | hge
        · exact hhiT.2 i (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi').1, hlt⟩)
        · have : i = hi := by have := (Finset.mem_Ico.mp hi').2; omega
          rw [this]; exact hin
      have := Finset.le_max' T (hi + 1) hmem
      rw [← hhidef] at this
      omega
  have hpelo : pe n (lo - 1) ∉ S := by
    by_cases h1 : lo = 1
    · rw [h1]
      simp only [Nat.sub_self]
      rw [pe_zero]
      exact hspoke 1 (by omega) (by omega)
    · intro hin
      have hmem : lo - 1 ∈ L := by
        simp only [hLdef, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        intro i hi'
        rcases Nat.lt_or_ge (lo - 1) i with hlt | hge
        · exact hloL.2 i (Finset.mem_Ico.mpr ⟨by omega, (Finset.mem_Ico.mp hi').2⟩)
        · have : i = lo - 1 := by have := (Finset.mem_Ico.mp hi').1; omega
          rw [this]; exact hin
      have := Finset.min'_le L (lo - 1) hmem
      rw [← hlodef] at this
      omega
  refine ⟨lo, hi, hlo1, hlov, hvhi, hhin, ?_, ?_⟩
  · intro e he
    simp only [Op, Finset.mem_image, Finset.mem_Ico] at he
    obtain ⟨i, ⟨ha, hb⟩, rfl⟩ := he
    exact hopen i ha hb
  · rw [Finset.disjoint_right]
    intro e he hes
    simp only [Cl, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton] at he
    rcases he with ⟨i, ⟨ha, hb⟩, rfl⟩ | rfl | rfl
    · exact hspoke i ha hb hes
    · exact hpelo hes
    · exact hpehi hes

/-! ## Part 4: uniqueness of blocks -/

private lemma blk_hi_unique {n k k' : ℕ} {S : Finset (Sym2 (Fin (n + 1)))}
    (hk : Blk n 1 k S) (hk' : Blk n 1 k' S) (h1 : 1 ≤ k) (h1' : 1 ≤ k') : k = k' := by
  rcases lt_trichotomy k k' with h | h | h
  · exact absurd (Blk_pe hk' h1 h) (Blk_pe_hi hk)
  · exact h
  · exact absurd (Blk_pe hk h1' h) (Blk_pe_hi hk')

private lemma blk_lo_unique {n l l' : ℕ} {S : Finset (Sym2 (Fin (n + 1)))}
    (hl : Blk n l n S) (hl' : Blk n l' n S) (h1 : 1 ≤ l) (h2 : l ≤ n) (h1' : 1 ≤ l')
    (h2' : l' ≤ n) : l = l' := by
  rcases lt_trichotomy l l' with h | h | h
  · exact absurd (Blk_pe hl (by omega) (by omega)) (Blk_pe_lo hl')
  · exact h
  · exact absurd (Blk_pe hl' (by omega) (by omega)) (Blk_pe_lo hl)

/-! ## Part 5: products over blocks -/

private lemma prod_pe_w {n : ℕ} (P : ℚ) (B : Finset ℕ) (hB : ∀ i ∈ B, 1 ≤ i ∧ i + 1 ≤ n) :
    ∏ e ∈ B.image (pe n), gadgetW n P e = P ^ B.card := by
  rw [Finset.prod_image (fun x hx y hy hxy =>
    pe_inj (hB x hx).1 (hB x hx).2 (hB y hy).1 (hB y hy).2 hxy)]
  rw [Finset.prod_congr rfl (fun i hi => w_pe P (hB i hi).1 (hB i hi).2), Finset.prod_const]

private lemma prod_cl_w {n : ℕ} (P : ℚ) (A B : Finset ℕ) (hA : ∀ i ∈ A, 1 ≤ i ∧ i ≤ n)
    (hB : ∀ i ∈ B, 1 ≤ i ∧ i + 1 ≤ n) :
    ∏ e ∈ (A.image (sp n) ∪ B.image (pe n)), (1 - gadgetW n P e)
      = P ^ A.card * (1 - P) ^ B.card := by
  have hdisj : Disjoint (A.image (sp n)) (B.image (pe n)) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp he'
    exact pe_ne_sp (hB j hj).1 (hB j hj).2 hje
  rw [Finset.prod_union hdisj]
  congr 1
  · rw [Finset.prod_image (fun x hx y hy hxy => sp_inj (hA x hx).1 (hA x hx).2 (hA y hy).2 hxy)]
    rw [Finset.prod_congr rfl (fun i _ => by rw [w_sp]; ring : ∀ i ∈ A, 1 - gadgetW n P (sp n i) = P),
      Finset.prod_const]
  · rw [Finset.prod_image (fun x hx y hy hxy =>
      pe_inj (hB x hx).1 (hB x hx).2 (hB y hy).1 (hB y hy).2 hxy)]
    rw [Finset.prod_congr rfl (fun i hi => by rw [w_pe P (hB i hi).1 (hB i hi).2] :
      ∀ i ∈ B, 1 - gadgetW n P (pe n i) = 1 - P), Finset.prod_const]

private lemma Cl_lo1 {n k : ℕ} (h1 : 1 ≤ k) :
    Cl n 1 k = (Finset.Icc 1 k).image (sp n) ∪ ({k} : Finset ℕ).image (pe n) := by
  have hmem : sp n 1 ∈ (Finset.Icc 1 k).image (sp n) ∪ ({pe n k} : Finset (Sym2 (Fin (n + 1)))) :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, h1⟩, rfl⟩)
  rw [Cl, Finset.image_singleton, show (1 : ℕ) - 1 = 0 from rfl, pe_zero,
    show ({sp n 1, pe n k} : Finset (Sym2 (Fin (n + 1)))) = insert (sp n 1) {pe n k} from rfl,
    Finset.union_insert, Finset.insert_eq_self.mpr hmem]

private lemma Cl_hin {n l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ n) :
    Cl n l n = (Finset.Icc l n).image (sp n) ∪ ({l - 1} : Finset ℕ).image (pe n) := by
  have hmem : sp n n ∈ (Finset.Icc l n).image (sp n) ∪
      ({pe n (l - 1)} : Finset (Sym2 (Fin (n + 1)))) :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨h2, le_rfl⟩, rfl⟩)
  rw [Cl, Finset.image_singleton, pe_top, Finset.pair_comm,
    show ({sp n n, pe n (l - 1)} : Finset (Sym2 (Fin (n + 1)))) = insert (sp n n) {pe n (l - 1)}
      from rfl,
    Finset.union_insert, Finset.insert_eq_self.mpr hmem]

private lemma Cl_full {n : ℕ} (h1 : 1 ≤ n) :
    Cl n 1 n = (Finset.Icc 1 n).image (sp n) ∪ (∅ : Finset ℕ).image (pe n) := by
  rw [Cl_hin (le_refl 1) h1, Finset.image_empty, Finset.union_empty, Finset.image_singleton,
    show (1 : ℕ) - 1 = 0 from rfl, pe_zero]
  refine Finset.union_eq_left.mpr ?_
  intro e he
  rw [Finset.mem_singleton] at he
  rw [he]
  exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, h1⟩, rfl⟩

/-! ## Part 6: the value of a block cylinder -/

private lemma master {n : ℕ} (P : ℚ) (A B B' : Finset ℕ)
    (hA : ∀ i ∈ A, 1 ≤ i ∧ i ≤ n) (hB : ∀ i ∈ B, 1 ≤ i ∧ i + 1 ≤ n)
    (hB' : ∀ i ∈ B', 1 ≤ i ∧ i + 1 ≤ n) (hd : Disjoint B' B) :
    ∑ S ∈ (gadgetE n).powerset,
      (if B'.image (pe n) ⊆ S ∧ Disjoint S (A.image (sp n) ∪ B.image (pe n))
        then weight (gadgetE n) (gadgetW n P) S else 0)
      = P ^ B'.card * (P ^ A.card * (1 - P) ^ B.card) := by
  have hO : B'.image (pe n) ⊆ gadgetE n := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact pe_mem (hB' i hi).1 (hB' i hi).2
  have hC : A.image (sp n) ∪ B.image (pe n) ⊆ gadgetE n := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact sp_mem (hA i hi).1 (hA i hi).2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact pe_mem (hB i hi).1 (hB i hi).2
  have hdisj : Disjoint (B'.image (pe n)) (A.image (sp n) ∪ B.image (pe n)) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_union.mp he' with h | h
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      exact pe_ne_sp (hB' i hi).1 (hB' i hi).2 hje.symm
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      have : i = j := pe_inj (hB' i hi).1 (hB' i hi).2 (hB j hj).1 (hB j hj).2 hje.symm
      exact (Finset.disjoint_left.mp hd hi) (this ▸ hj)
  rw [cyl (gadgetE n) _ _ (gadgetW n P) hO hC hdisj, prod_pe_w P B' hB',
    prod_cl_w P A B hA hB]

private lemma V1 {n k : ℕ} (P : ℚ) (h1 : 1 ≤ k) (h2 : k + 1 ≤ n) :
    ∑ S ∈ (gadgetE n).powerset,
      (if Blk n 1 k S then weight (gadgetE n) (gadgetW n P) S else 0)
      = P ^ (k - 1) * (P ^ k * (1 - P)) := by
  have hmas := master (n := n) P (Finset.Icc 1 k) {k} (Finset.Ico 1 k)
    (fun i hi => ⟨(Finset.mem_Icc.mp hi).1, le_trans (Finset.mem_Icc.mp hi).2 (by omega)⟩)
    (fun i hi => by rw [Finset.mem_singleton] at hi; omega)
    (fun i hi => by have := Finset.mem_Ico.mp hi; omega)
    (by
      rw [Finset.disjoint_right]
      intro i hi
      rw [Finset.mem_singleton] at hi
      simp only [Finset.mem_Ico, hi]
      omega)
  rw [Nat.card_Icc, Nat.card_Ico, Finset.card_singleton] at hmas
  rw [show k + 1 - 1 = k from rfl] at hmas
  rw [show (1 : ℚ) - P = ((1 : ℚ) - P) ^ 1 from (pow_one _).symm]
  rw [← hmas]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine if_congr ?_ rfl rfl
  rw [Blk, Op, Cl_lo1 h1, Finset.image_singleton]

private lemma V1' {n : ℕ} (P : ℚ) (h1 : 1 ≤ n) :
    ∑ S ∈ (gadgetE n).powerset,
      (if Blk n 1 n S then weight (gadgetE n) (gadgetW n P) S else 0)
      = P ^ (n - 1) * P ^ n := by
  have hmas := master (n := n) P (Finset.Icc 1 n) ∅ (Finset.Ico 1 n)
    (fun i hi => Finset.mem_Icc.mp hi)
    (fun i hi => by simp at hi)
    (fun i hi => by have := Finset.mem_Ico.mp hi; omega)
    (Finset.disjoint_empty_right _)
  rw [Nat.card_Icc, Nat.card_Ico, Finset.card_empty, pow_zero, mul_one,
    show n + 1 - 1 = n from rfl] at hmas
  rw [← hmas]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine if_congr ?_ rfl rfl
  rw [Blk, Op, Cl_full h1]

private lemma V2 {n l : ℕ} (P : ℚ) (h1 : 2 ≤ l) (h2 : l ≤ n) :
    ∑ S ∈ (gadgetE n).powerset,
      (if Blk n l n S then weight (gadgetE n) (gadgetW n P) S else 0)
      = P ^ (n - l) * (P ^ (n + 1 - l) * (1 - P)) := by
  have hmas := master (n := n) P (Finset.Icc l n) {l - 1} (Finset.Ico l n)
    (fun i hi => ⟨le_trans (by omega) (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2⟩)
    (fun i hi => by rw [Finset.mem_singleton] at hi; omega)
    (fun i hi => by have := Finset.mem_Ico.mp hi; omega)
    (by
      rw [Finset.disjoint_right]
      intro i hi
      rw [Finset.mem_singleton] at hi
      simp only [Finset.mem_Ico, hi]
      omega)
  rw [Nat.card_Icc, Nat.card_Ico, Finset.card_singleton] at hmas
  rw [show (1 : ℚ) - P = ((1 : ℚ) - P) ^ 1 from (pow_one _).symm]
  rw [← hmas]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine if_congr ?_ rfl rfl
  rw [Blk, Op, Cl_hin (by omega) h2, Finset.image_singleton]

private lemma V3 {n k l : ℕ} (P : ℚ) (h1 : 1 ≤ k) (h2 : k < l) (h3 : l ≤ n) :
    ∑ S ∈ (gadgetE n).powerset,
      (if Blk n 1 k S ∧ Blk n l n S then weight (gadgetE n) (gadgetW n P) S else 0)
      = P ^ ((k - 1) + (n - l)) * (P ^ (k + (n + 1 - l)) * (1 - P) ^ ({k} ∪ {l - 1} : Finset ℕ).card)
    := by
  have hmas := master (n := n) P (Finset.Icc 1 k ∪ Finset.Icc l n) ({k} ∪ {l - 1})
    (Finset.Ico 1 k ∪ Finset.Ico l n)
    (by
      intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · have := Finset.mem_Icc.mp h; omega
      · have := Finset.mem_Icc.mp h; omega)
    (by
      intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · rw [Finset.mem_singleton] at h; omega
      · rw [Finset.mem_singleton] at h; omega)
    (by
      intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · have := Finset.mem_Ico.mp h; omega
      · have := Finset.mem_Ico.mp h; omega)
    (by
      rw [Finset.disjoint_left]
      intro i hi hi'
      rcases Finset.mem_union.mp hi with h | h
      · have := Finset.mem_Ico.mp h
        rcases Finset.mem_union.mp hi' with h' | h' <;>
          rw [Finset.mem_singleton] at h' <;> omega
      · have := Finset.mem_Ico.mp h
        rcases Finset.mem_union.mp hi' with h' | h' <;>
          rw [Finset.mem_singleton] at h' <;> omega)
  have hcA : (Finset.Icc 1 k ∪ Finset.Icc l n).card = k + (n + 1 - l) := by
    rw [Finset.card_union_of_disjoint, Nat.card_Icc, Nat.card_Icc]
    · omega
    · rw [Finset.disjoint_left]
      intro i hi hi'
      have := Finset.mem_Icc.mp hi
      have := Finset.mem_Icc.mp hi'
      omega
  have hcB : (Finset.Ico 1 k ∪ Finset.Ico l n).card = (k - 1) + (n - l) := by
    rw [Finset.card_union_of_disjoint, Nat.card_Ico, Nat.card_Ico]
    · rw [Finset.disjoint_left]
      intro i hi hi'
      have := Finset.mem_Ico.mp hi
      have := Finset.mem_Ico.mp hi'
      omega
  rw [hcA, hcB] at hmas
  rw [← hmas]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine if_congr ?_ rfl rfl
  rw [Blk, Blk, Op, Op, Cl_lo1 h1, Cl_hin (by omega) h3]
  simp only [Finset.image_union, Finset.image_singleton, Finset.union_subset_iff,
    Finset.disjoint_union_right]
  tauto

/-! ## Part 7: the indicator identities -/

private lemma cast_one {n : ℕ} : ((1 : ℕ) : Fin (n + 1)) = 1 := by simp

private lemma cast_last {n : ℕ} : ((n : ℕ) : Fin (n + 1)) = Fin.last n := by
  apply Fin.ext
  rw [vc le_rfl, Fin.val_last]

private lemma claim1 {n : ℕ} (hn : 1 ≤ n) {S : Finset (Sym2 (Fin (n + 1)))}
    (hS : S ⊆ gadgetE n) :
    ∑ j ∈ Finset.range n, (if Blk n 1 (j + 1) S then (1 : ℚ) else 0)
      = if (ofEdges S).Reachable 0 (1 : Fin (n + 1)) then 0 else 1 := by
  by_cases hR : (ofEdges S).Reachable 0 (1 : Fin (n + 1))
  · rw [if_pos hR]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [if_neg]
    intro hB
    have hj' := Finset.mem_range.mp hj
    exact not_reach (v := 1) hS le_rfl (by omega) hB le_rfl (by omega)
      (by rw [cast_one]; exact hR)
  · rw [if_neg hR]
    obtain ⟨lo, hi, hlo1, hlov, hvhi, hhin, hB⟩ :=
      exists_blk hS (v := 1) le_rfl hn (by rw [cast_one]; exact hR)
    have hlo : lo = 1 := by omega
    rw [hlo] at hB
    have hkey : ∀ b ∈ Finset.range n, b ≠ hi - 1 →
        (if Blk n 1 (b + 1) S then (1 : ℚ) else 0) = 0 := by
      intro b _ hne
      rw [if_neg]
      intro hB'
      have := blk_hi_unique hB' hB (by omega) (by omega)
      omega
    rw [Finset.sum_eq_single_of_mem (hi - 1) (Finset.mem_range.mpr (by omega)) hkey,
      show hi - 1 + 1 = hi from by omega, if_pos hB]

private lemma claim2 {n : ℕ} (hn : 1 ≤ n) {S : Finset (Sym2 (Fin (n + 1)))}
    (hS : S ⊆ gadgetE n) :
    ∑ i ∈ Finset.range n, (if Blk n (n - i) n S then (1 : ℚ) else 0)
      = if (ofEdges S).Reachable 0 (Fin.last n) then 0 else 1 := by
  by_cases hR : (ofEdges S).Reachable 0 (Fin.last n)
  · rw [if_pos hR]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [if_neg]
    intro hB
    have hi' := Finset.mem_range.mp hi
    exact not_reach (v := n) hS (by omega) le_rfl hB (by omega) le_rfl
      (by rw [cast_last]; exact hR)
  · rw [if_neg hR]
    obtain ⟨lo, hi, hlo1, hlov, hvhi, hhin, hB⟩ :=
      exists_blk hS (v := n) hn le_rfl (by rw [cast_last]; exact hR)
    have hhi : hi = n := by omega
    rw [hhi] at hB
    have hkey : ∀ b ∈ Finset.range n, b ≠ n - lo →
        (if Blk n (n - b) n S then (1 : ℚ) else 0) = 0 := by
      intro b hb hne
      rw [if_neg]
      intro hB'
      have hb' := Finset.mem_range.mp hb
      have := blk_lo_unique hB' hB (by omega) (by omega) (by omega) (by omega)
      omega
    rw [Finset.sum_eq_single_of_mem (n - lo) (Finset.mem_range.mpr (by omega)) hkey,
      show n - (n - lo) = lo from by omega, if_pos hB]

private lemma claim3 {n : ℕ} (hn : 3 ≤ n) {S : Finset (Sym2 (Fin (n + 1)))}
    (hS : S ⊆ gadgetE n) :
    (∑ s ∈ Finset.range (n - 1), ∑ j ∈ Finset.range (s + 1),
        (if Blk n 1 (j + 1) S ∧ Blk n (n - s + j) n S then (1 : ℚ) else 0))
      + (if Blk n 1 n S then (1 : ℚ) else 0)
      = if ((ofEdges S).Reachable 0 (1 : Fin (n + 1)) ∨
            (ofEdges S).Reachable 0 (Fin.last n)) then 0 else 1 := by
  by_cases hR : (ofEdges S).Reachable 0 (1 : Fin (n + 1)) ∨
      (ofEdges S).Reachable 0 (Fin.last n)
  · rw [if_pos hR]
    have hzero : ∀ s ∈ Finset.range (n - 1), ∀ j ∈ Finset.range (s + 1),
        (if Blk n 1 (j + 1) S ∧ Blk n (n - s + j) n S then (1 : ℚ) else 0) = 0 := by
      intro s hs j hj
      have hs' := Finset.mem_range.mp hs
      have hj' := Finset.mem_range.mp hj
      rw [if_neg]
      intro hBB
      rcases hR with h | h
      · exact not_reach (v := 1) hS le_rfl (by omega) hBB.1 le_rfl (by omega)
          (by rw [cast_one]; exact h)
      · exact not_reach (v := n) hS (by omega) le_rfl hBB.2 (by omega) le_rfl
          (by rw [cast_last]; exact h)
    rw [Finset.sum_congr rfl (fun s hs => Finset.sum_eq_zero (hzero s hs))]
    rw [if_neg, Finset.sum_const_zero, add_zero]
    intro hfull
    rcases hR with h | h
    · exact not_reach (v := 1) hS le_rfl le_rfl hfull le_rfl (by omega)
        (by rw [cast_one]; exact h)
    · exact not_reach (v := n) hS le_rfl le_rfl hfull (by omega) le_rfl
        (by rw [cast_last]; exact h)
  · rw [if_neg hR]
    push_neg at hR
    obtain ⟨hR1, hR2⟩ := hR
    obtain ⟨lo1, k, ha1, ha2, ha3, ha4, hBk0⟩ :=
      exists_blk hS (v := 1) le_rfl (by omega) (by rw [cast_one]; exact hR1)
    obtain ⟨l, hi2, hb1, hb2, hb3, hb4, hBl0⟩ :=
      exists_blk hS (v := n) (by omega) le_rfl (by rw [cast_last]; exact hR2)
    have hlo1 : lo1 = 1 := by omega
    have hhi2 : hi2 = n := by omega
    rw [hlo1] at hBk0
    rw [hhi2] at hBl0
    by_cases hkl : k < l
    · have hlast : (if Blk n 1 n S then (1 : ℚ) else 0) = 0 := by
        rw [if_neg]
        intro hfull
        have e1 : n = k := blk_hi_unique hfull hBk0 (by omega) (by omega)
        have e2 : 1 = l := blk_lo_unique hfull hBl0 (by omega) (by omega) (by omega) (by omega)
        omega
      rw [hlast, add_zero]
      have hkey : ∀ s ∈ Finset.range (n - 1), s ≠ (k - 1) + (n - l) →
          (∑ j ∈ Finset.range (s + 1),
            (if Blk n 1 (j + 1) S ∧ Blk n (n - s + j) n S then (1 : ℚ) else 0)) = 0 := by
        intro s hs hne
        have hs' := Finset.mem_range.mp hs
        refine Finset.sum_eq_zero (fun j hj => ?_)
        have hj' := Finset.mem_range.mp hj
        rw [if_neg]
        intro hBB
        have e1 := blk_hi_unique hBB.1 hBk0 (by omega) (by omega)
        have e2 := blk_lo_unique hBB.2 hBl0 (by omega) (by omega) (by omega) (by omega)
        omega
      rw [Finset.sum_eq_single_of_mem ((k - 1) + (n - l))
        (Finset.mem_range.mpr (by omega)) hkey]
      have hkey2 : ∀ b ∈ Finset.range ((k - 1) + (n - l) + 1), b ≠ k - 1 →
          (if Blk n 1 (b + 1) S ∧ Blk n (n - ((k - 1) + (n - l)) + b) n S
            then (1 : ℚ) else 0) = 0 := by
        intro b hb hne
        have hb' := Finset.mem_range.mp hb
        rw [if_neg]
        intro hBB
        have e1 := blk_hi_unique hBB.1 hBk0 (by omega) (by omega)
        omega
      rw [Finset.sum_eq_single_of_mem (k - 1) (Finset.mem_range.mpr (by omega)) hkey2,
        show k - 1 + 1 = k from by omega,
        show n - ((k - 1) + (n - l)) + (k - 1) = l from by omega,
        if_pos ⟨hBk0, hBl0⟩]
    · have hall : ∀ i, 1 ≤ i → i < n → pe n i ∈ S := by
        intro i h1 h2
        rcases Nat.lt_or_ge i k with h | h
        · exact Blk_pe hBk0 h1 h
        · exact Blk_pe hBl0 (by omega) h2
      have hkn : k = n := by
        by_contra hne
        exact Blk_pe_hi hBk0 (hall k (by omega) (by omega))
      have hl1 : l = 1 := by
        by_contra hne
        exact Blk_pe_lo hBl0 (hall (l - 1) (by omega) (by omega))
      rw [hkn] at hBk0
      have hzero : ∀ s ∈ Finset.range (n - 1), ∀ j ∈ Finset.range (s + 1),
          (if Blk n 1 (j + 1) S ∧ Blk n (n - s + j) n S then (1 : ℚ) else 0) = 0 := by
        intro s hs j hj
        have hs' := Finset.mem_range.mp hs
        have hj' := Finset.mem_range.mp hj
        rw [if_neg]
        intro hBB
        have e1 := blk_hi_unique hBB.1 hBk0 (by omega) (by omega)
        have e2 := blk_lo_unique hBB.2 hBl0 (by omega) (by omega) (by omega) (by omega)
        omega
      rw [Finset.sum_congr rfl (fun s hs => Finset.sum_eq_zero (hzero s hs)),
        Finset.sum_const_zero, zero_add, if_pos hBk0]

/-! ## Part 8: arithmetic helpers -/

private lemma geo (P : ℚ) (N : ℕ) :
    (1 - P ^ 2) * ∑ j ∈ Finset.range N, P ^ (2 * j) = 1 - P ^ (2 * N) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

private lemma ari (P : ℚ) (N : ℕ) :
    (1 - P ^ 2) ^ 2 * ∑ s ∈ Finset.range N, ((s : ℚ) + 1) * P ^ (2 * s)
      = 1 - ((N : ℚ) + 1) * P ^ (2 * N) + (N : ℚ) * P ^ (2 * N + 2) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, mul_add, ih]; push_cast; ring

private lemma algebra (m : ℕ) (P : ℚ) (SA SB : ℚ) (hP0 : 0 < P) (hP1 : P < 1)
    (hA : (1 - P ^ 2) * SA = 1 - P ^ (2 * m + 4))
    (hB : (1 - P ^ 2) ^ 2 * SB = 1 - ((m : ℚ) + 2) * P ^ (2 * m + 2)
      + ((m : ℚ) + 1) * P ^ (2 * m + 4)) :
    1 - 2 * ((1 - P) * P * SA + P ^ (2 * m + 5))
      + ((1 - P) ^ 2 * P ^ 2 * SB + ((m : ℚ) + 2) * (1 - P) * P ^ (2 * m + 4)
        + P ^ (2 * m + 5))
      = (1 - P ^ (2 * m + 6)) / (1 + P) ^ 2
        + ((m : ℚ) + 3) * (1 - P) * P ^ (2 * m + 5) / (1 + P) := by
  have h1 : (1 : ℚ) - P ≠ 0 := by linarith
  have h2 : (1 : ℚ) + P ≠ 0 := by linarith
  have hsq : (1 : ℚ) - P ^ 2 = (1 - P) * (1 + P) := by ring
  rw [hsq] at hA hB
  have hSA : SA = (1 - P ^ (2 * m + 4)) / ((1 - P) * (1 + P)) := by
    field_simp at hA ⊢; linarith [hA]
  have hSB : SB = (1 - ((m : ℚ) + 2) * P ^ (2 * m + 2) + ((m : ℚ) + 1) * P ^ (2 * m + 4))
      / ((1 - P) * (1 + P)) ^ 2 := by
    field_simp at hB ⊢; linarith [hB]
  rw [hSA, hSB]
  field_simp
  ring

private lemma ind_id {n : ℕ} (S : Finset (Sym2 (Fin (n + 1)))) :
    (if ((ofEdges S).Reachable 0 1 ∧ (ofEdges S).Reachable 1 (Fin.last n)) then (1 : ℚ) else 0)
      = 1 - (if (ofEdges S).Reachable 0 (1 : Fin (n + 1)) then 0 else 1)
        - (if (ofEdges S).Reachable 0 (Fin.last n) then 0 else 1)
        + (if ((ofEdges S).Reachable 0 (1 : Fin (n + 1)) ∨
              (ofEdges S).Reachable 0 (Fin.last n)) then 0 else 1) := by
  by_cases h1 : (ofEdges S).Reachable 0 (1 : Fin (n + 1))
  · by_cases h2 : (ofEdges S).Reachable 0 (Fin.last n)
    · rw [if_pos ⟨h1, h1.symm.trans h2⟩, if_pos h1, if_pos h2, if_pos (Or.inl h1)]
      norm_num
    · rw [if_neg (fun h => h2 (h1.trans h.2)), if_pos h1, if_neg h2, if_pos (Or.inl h1)]
      norm_num
  · rw [if_neg (fun h => h1 h.1), if_neg h1]
    by_cases h2 : (ofEdges S).Reachable 0 (Fin.last n)
    · rw [if_pos h2, if_pos (Or.inr h2)]; norm_num
    · rw [if_neg h2, if_neg (fun h => h.elim h1 h2)]; norm_num

/-! ## Part 9: reduction of `Pabc` to block cylinders -/

private lemma ite_w {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (S : Finset (Sym2 V)) (p : Prop) [Decidable p] :
    (if p then weight E w S else (0 : ℚ)) = (if p then (1 : ℚ) else 0) * weight E w S := by
  split_ifs <;> ring

private lemma reduce {n : ℕ} (P : ℚ) (hn : 3 ≤ n) :
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      = 1 - (∑ j ∈ Finset.range n, ∑ S ∈ (gadgetE n).powerset,
              (if Blk n 1 (j + 1) S then weight (gadgetE n) (gadgetW n P) S else 0))
          - (∑ i ∈ Finset.range n, ∑ S ∈ (gadgetE n).powerset,
              (if Blk n (n - i) n S then weight (gadgetE n) (gadgetW n P) S else 0))
          + ((∑ s ∈ Finset.range (n - 1), ∑ j ∈ Finset.range (s + 1),
                ∑ S ∈ (gadgetE n).powerset,
                (if Blk n 1 (j + 1) S ∧ Blk n (n - s + j) n S then
                  weight (gadgetE n) (gadgetW n P) S else 0))
             + (∑ S ∈ (gadgetE n).powerset,
                (if Blk n 1 n S then weight (gadgetE n) (gadgetW n P) S else 0))) := by
  have hpoint : ∀ S ∈ (gadgetE n).powerset,
      (if ((ofEdges S).Reachable 0 1 ∧ (ofEdges S).Reachable 1 (Fin.last n)) then
          weight (gadgetE n) (gadgetW n P) S else 0)
        = weight (gadgetE n) (gadgetW n P) S
          - (∑ j ∈ Finset.range n,
              (if Blk n 1 (j + 1) S then weight (gadgetE n) (gadgetW n P) S else 0))
          - (∑ i ∈ Finset.range n,
              (if Blk n (n - i) n S then weight (gadgetE n) (gadgetW n P) S else 0))
          + ((∑ s ∈ Finset.range (n - 1), ∑ j ∈ Finset.range (s + 1),
                (if Blk n 1 (j + 1) S ∧ Blk n (n - s + j) n S then
                  weight (gadgetE n) (gadgetW n P) S else 0))
             + (if Blk n 1 n S then weight (gadgetE n) (gadgetW n P) S else 0)) := by
    intro S hS
    have hSs := Finset.mem_powerset.mp hS
    have e1 := claim1 (show 1 ≤ n by omega) hSs
    have e2 := claim2 (show 1 ≤ n by omega) hSs
    have e3 := claim3 hn hSs
    have key : (if ((ofEdges S).Reachable 0 1 ∧ (ofEdges S).Reachable 1 (Fin.last n)) then
          (1 : ℚ) else 0)
        = 1 - (∑ j ∈ Finset.range n, (if Blk n 1 (j + 1) S then (1 : ℚ) else 0))
            - (∑ i ∈ Finset.range n, (if Blk n (n - i) n S then (1 : ℚ) else 0))
            + ((∑ s ∈ Finset.range (n - 1), ∑ j ∈ Finset.range (s + 1),
                  (if Blk n 1 (j + 1) S ∧ Blk n (n - s + j) n S then (1 : ℚ) else 0))
               + (if Blk n 1 n S then (1 : ℚ) else 0)) := by
      rw [e1, e2, e3]
      exact ind_id S
    rw [ite_w, key]
    simp only [sub_mul, add_mul, one_mul, Finset.sum_mul, ← ite_w]
  have sw1 : ∀ F : Finset (Sym2 (Fin (n + 1))) → ℕ → ℚ,
      ∑ S ∈ (gadgetE n).powerset, ∑ j ∈ Finset.range n, F S j
        = ∑ j ∈ Finset.range n, ∑ S ∈ (gadgetE n).powerset, F S j := fun _ => Finset.sum_comm
  have sw3 : ∀ F : Finset (Sym2 (Fin (n + 1))) → ℕ → ℕ → ℚ,
      ∑ S ∈ (gadgetE n).powerset, ∑ s ∈ Finset.range (n - 1), ∑ j ∈ Finset.range (s + 1), F S s j
        = ∑ s ∈ Finset.range (n - 1), ∑ j ∈ Finset.range (s + 1),
            ∑ S ∈ (gadgetE n).powerset, F S s j := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
  rw [Pabc, probOf, Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [total, sw1, sw1, sw3]

/-! ## Part 10: evaluating the four sums -/

private lemma card2 (a b : ℕ) (h : a ≠ b) : ({a} ∪ {b} : Finset ℕ).card = 2 := by
  rw [Finset.singleton_union]
  rw [Finset.card_pair h]

private lemma card1 (a : ℕ) : ({a} ∪ {a} : Finset ℕ).card = 1 := by
  rw [Finset.union_self, Finset.card_singleton]

private lemma E1 (m : ℕ) (P : ℚ) :
    (∑ j ∈ Finset.range (m + 3), ∑ S ∈ (gadgetE (m + 3)).powerset,
        (if Blk (m + 3) 1 (j + 1) S then
          weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0))
      = (1 - P) * P * (∑ j ∈ Finset.range (m + 2), P ^ (2 * j)) + P ^ (2 * m + 5) := by
  rw [Finset.sum_range_succ]
  have step : ∀ j ∈ Finset.range (m + 2),
      (∑ S ∈ (gadgetE (m + 3)).powerset, (if Blk (m + 3) 1 (j + 1) S then
        weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0)) = (1 - P) * P * P ^ (2 * j) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [V1 P (by omega) (by omega), Nat.add_sub_cancel]
    ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum,
    show m + 2 + 1 = m + 3 from rfl, V1' P (by omega), show m + 3 - 1 = m + 2 from by omega]
  ring

private lemma E2 (m : ℕ) (P : ℚ) :
    (∑ i ∈ Finset.range (m + 3), ∑ S ∈ (gadgetE (m + 3)).powerset,
        (if Blk (m + 3) (m + 3 - i) (m + 3) S then
          weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0))
      = (1 - P) * P * (∑ j ∈ Finset.range (m + 2), P ^ (2 * j)) + P ^ (2 * m + 5) := by
  rw [Finset.sum_range_succ]
  have step : ∀ i ∈ Finset.range (m + 2),
      (∑ S ∈ (gadgetE (m + 3)).powerset, (if Blk (m + 3) (m + 3 - i) (m + 3) S then
        weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0)) = (1 - P) * P * P ^ (2 * i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [V2 P (by omega) (by omega), show m + 3 - (m + 3 - i) = i from by omega,
      show m + 3 + 1 - (m + 3 - i) = i + 1 from by omega]
    ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum,
    show m + 3 - (m + 2) = 1 from by omega, V1' P (by omega),
    show m + 3 - 1 = m + 2 from by omega]
  ring

private lemma E4 (m : ℕ) (P : ℚ) :
    (∑ S ∈ (gadgetE (m + 3)).powerset, (if Blk (m + 3) 1 (m + 3) S then
      weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0)) = P ^ (2 * m + 5) := by
  rw [V1' P (by omega), show m + 3 - 1 = m + 2 from by omega]
  ring

private lemma E3 (m : ℕ) (P : ℚ) :
    (∑ s ∈ Finset.range (m + 2), ∑ j ∈ Finset.range (s + 1),
        ∑ S ∈ (gadgetE (m + 3)).powerset,
        (if Blk (m + 3) 1 (j + 1) S ∧ Blk (m + 3) (m + 3 - s + j) (m + 3) S then
          weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0))
      = (1 - P) ^ 2 * P ^ 2 * (∑ s ∈ Finset.range (m + 1), ((s : ℚ) + 1) * P ^ (2 * s))
        + ((m : ℚ) + 2) * (1 - P) * P ^ (2 * m + 4) := by
  rw [Finset.sum_range_succ]
  have step : ∀ s ∈ Finset.range (m + 1),
      (∑ j ∈ Finset.range (s + 1), ∑ S ∈ (gadgetE (m + 3)).powerset,
        (if Blk (m + 3) 1 (j + 1) S ∧ Blk (m + 3) (m + 3 - s + j) (m + 3) S then
          weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0))
        = (1 - P) ^ 2 * P ^ 2 * (((s : ℚ) + 1) * P ^ (2 * s)) := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have inner : ∀ j ∈ Finset.range (s + 1),
        (∑ S ∈ (gadgetE (m + 3)).powerset,
          (if Blk (m + 3) 1 (j + 1) S ∧ Blk (m + 3) (m + 3 - s + j) (m + 3) S then
            weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0))
          = P ^ s * (P ^ (s + 2) * (1 - P) ^ 2) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [V3 P (by omega) (by omega) (by omega),
        show j + 1 - 1 + (m + 3 - (m + 3 - s + j)) = s from by omega,
        show j + 1 + (m + 3 + 1 - (m + 3 - s + j)) = s + 2 from by omega,
        card2 (j + 1) (m + 3 - s + j - 1) (by omega)]
    rw [Finset.sum_congr rfl inner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
  have diag : ∀ j ∈ Finset.range (m + 1 + 1),
      (∑ S ∈ (gadgetE (m + 3)).powerset,
        (if Blk (m + 3) 1 (j + 1) S ∧ Blk (m + 3) (m + 3 - (m + 1) + j) (m + 3) S then
          weight (gadgetE (m + 3)) (gadgetW (m + 3) P) S else 0))
        = P ^ (m + 1) * (P ^ (m + 3) * (1 - P) ^ 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [V3 P (by omega) (by omega) (by omega),
      show j + 1 - 1 + (m + 3 - (m + 3 - (m + 1) + j)) = m + 1 from by omega,
      show j + 1 + (m + 3 + 1 - (m + 3 - (m + 1) + j)) = m + 3 from by omega,
      show m + 3 - (m + 1) + j - 1 = j + 1 from by omega, card1 (j + 1)]
  rw [Finset.sum_congr rfl diag, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-! ## The theorem -/

theorem solution (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      = (1 - P ^ (2 * n)) / (1 + P) ^ 2 + n * (1 - P) * P ^ (2 * n - 1) / (1 + P) := by
  rw [reduce P hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 from by omega, E1, E2, E3, E4,
    show 2 * (m + 3) = 2 * m + 6 from by omega,
    show 2 * m + 6 - 1 = 2 * m + 5 from by omega]
  have hAA : (1 - P ^ 2) * (∑ j ∈ Finset.range (m + 2), P ^ (2 * j)) = 1 - P ^ (2 * m + 4) := by
    have h := geo P (m + 2); linear_combination h
  have hBB : (1 - P ^ 2) ^ 2 * (∑ s ∈ Finset.range (m + 1), ((s : ℚ) + 1) * P ^ (2 * s))
      = 1 - ((m : ℚ) + 2) * P ^ (2 * m + 2) + ((m : ℚ) + 1) * P ^ (2 * m + 4) := by
    have h := ari P (m + 1); push_cast at h; linear_combination h
  push_cast
  linear_combination algebra m P (∑ j ∈ Finset.range (m + 2), P ^ (2 * j))
    (∑ s ∈ Finset.range (m + 1), ((s : ℚ) + 1) * P ^ (2 * s)) hP0 hP1 hAA hBB
