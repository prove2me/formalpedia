-- Prove2me | solution 1 for CompOT.Vertices.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:14:48.182911+00:00
-- url     : https://prove2.me/submissions/aa58bafa-e00a-42de-88a4-fbaad32273c9

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

set_option autoImplicit false
open CompOT.Vertices Filter Topology


namespace CycAux

variable {n m : ℕ}

/-- elementary matrix of an undirected pair of nodes -/
noncomputable def Mx (u y : Fin n ⊕ Fin m) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => if s(u, y) = s(Sum.inl i, Sum.inr j) then 1 else 0

/-- alternating sum of elementary matrices along a walk -/
noncomputable def Fw (P : Matrix (Fin n) (Fin m) ℝ) :
    {u v : Fin n ⊕ Fin m} → (supportGraph P).Walk u v → Matrix (Fin n) (Fin m) ℝ
  | _, _, SimpleGraph.Walk.nil => 0
  | u, _, SimpleGraph.Walk.cons (v := x) _ w => Mx u x - Fw P w

/-- row/column sum at a node -/
def Sx (x : Fin n ⊕ Fin m) (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  Sum.elim (fun i => ∑ j, A i j) (fun j => ∑ i, A i j) x

lemma Sx_sub (x : Fin n ⊕ Fin m) (A B : Matrix (Fin n) (Fin m) ℝ) :
    Sx x (A - B) = Sx x A - Sx x B := by
  cases x <;> simp [Sx, Finset.sum_sub_distrib]

lemma Sx_zero (x : Fin n ⊕ Fin m) : Sx x (0 : Matrix (Fin n) (Fin m) ℝ) = 0 := by
  cases x <;> simp [Sx]

lemma Mx_lr (i0 : Fin n) (j1 : Fin m) (i : Fin n) (j : Fin m) :
    Mx (Sum.inl i0) (Sum.inr j1) i j = if i = i0 ∧ j = j1 then 1 else 0 := by
  simp only [Mx, Matrix.of_apply, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    or_false]
  by_cases h1 : i0 = i <;> by_cases h2 : j1 = j <;> simp [h1, h2, eq_comm]

lemma Mx_rl (j0 : Fin m) (i1 : Fin n) (i : Fin n) (j : Fin m) :
    Mx (Sum.inr j0) (Sum.inl i1) i j = if i = i1 ∧ j = j0 then 1 else 0 := by
  simp only [Mx, Matrix.of_apply, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    false_or]
  by_cases h1 : i1 = i <;> by_cases h2 : j0 = j <;> simp [h1, h2, eq_comm]

lemma Sx_lr (i0 : Fin n) (j1 : Fin m) (x : Fin n ⊕ Fin m) :
    Sx x (Mx (Sum.inl i0) (Sum.inr j1)) =
      (if x = Sum.inl i0 then 1 else 0) + (if x = Sum.inr j1 then 1 else 0) := by
  cases x with
  | inl i =>
    simp only [Sx, Sum.elim_inl, Mx_lr]
    by_cases h : i = i0 <;> simp [h]
  | inr j =>
    simp only [Sx, Sum.elim_inr, Mx_lr]
    by_cases h : j = j1 <;> simp [h]

lemma Sx_Mx (P : Matrix (Fin n) (Fin m) ℝ) (x u y : Fin n ⊕ Fin m)
    (h : (supportGraph P).Adj u y) :
    Sx x (Mx u y) = (if x = u then 1 else 0) + (if x = y then 1 else 0) := by
  rcases u with i0 | j0 <;> rcases y with i1 | j1
  · exact absurd h (by simp [supportGraph, supportRel])
  · exact Sx_lr i0 j1 x
  · have : Mx (Sum.inr j0) (Sum.inl i1) = Mx (Sum.inl i1) (Sum.inr j0) := by
      funext i j; simp only [Mx, Matrix.of_apply, Sym2.eq_swap]
    rw [this, Sx_lr]; ring
  · exact absurd h (by simp [supportGraph, supportRel])

lemma Sx_Fw (P : Matrix (Fin n) (Fin m) ℝ) (x : Fin n ⊕ Fin m) {u v : Fin n ⊕ Fin m}
    (w : (supportGraph P).Walk u v) :
    Sx x (Fw P w) = (if x = u then 1 else 0) - (-1 : ℝ) ^ w.length * (if x = v then 1 else 0) := by
  induction w with
  | nil => simp [Fw, Sx_zero]
  | @cons u y v h w ih =>
    rw [Fw, Sx_sub, Sx_Mx P x u y h, ih, SimpleGraph.Walk.length_cons, pow_succ]
    ring

lemma isLeft_flip (P : Matrix (Fin n) (Fin m) ℝ) {u y : Fin n ⊕ Fin m}
    (h : (supportGraph P).Adj u y) : u.isLeft = !y.isLeft := by
  rcases u with i0 | j0 <;> rcases y with i1 | j1
  · exact absurd h (by simp [supportGraph, supportRel])
  · rfl
  · rfl
  · exact absurd h (by simp [supportGraph, supportRel])

lemma even_closed (P : Matrix (Fin n) (Fin m) ℝ) {u v : Fin n ⊕ Fin m}
    (w : (supportGraph P).Walk u v) : (Even w.length ↔ u.isLeft = v.isLeft) := by
  induction w with
  | nil => simp
  | @cons u y v h w ih =>
    have := isLeft_flip P h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ih, this]
    cases hy : y.isLeft <;> cases hv : v.isLeft <;> simp

lemma Fw_support (P : Matrix (Fin n) (Fin m) ℝ) {u v : Fin n ⊕ Fin m}
    (w : (supportGraph P).Walk u v) (i : Fin n) (j : Fin m) (h : Fw P w i j ≠ 0) :
    s(Sum.inl i, Sum.inr j) ∈ w.edges := by
  induction w with
  | nil => simp [Fw] at h
  | @cons u y v hh w ih =>
    rw [Fw] at h
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
    by_cases h1 : Fw P w i j = 0
    · left
      rw [Matrix.sub_apply, h1, sub_zero] at h
      simp only [Mx, Matrix.of_apply] at h
      by_contra hne
      exact h (by simp [Ne.symm hne])
    · right; exact ih h1

lemma Fw_ne_zero (P : Matrix (Fin n) (Fin m) ℝ) {v : Fin n ⊕ Fin m}
    (c : (supportGraph P).Walk v v) (hc : c.IsCycle) : Fw P c ≠ 0 := by
  cases c with
  | nil => exact absurd hc (by simp)
  | @cons _ y _ h p =>
    rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
    obtain ⟨_, hnot⟩ := hc
    intro hz
    rcases v with i | j <;> rcases y with i' | j'
    · exact absurd h (by simp [supportGraph, supportRel])
    · have h0 := congrFun (congrFun hz i) j'
      have hz2 : Fw P p i j' = 0 := by
        by_contra hne
        exact hnot (Fw_support P p i j' hne)
      rw [Fw, Matrix.sub_apply, Mx_lr, hz2] at h0
      simp at h0
    · have h0 := congrFun (congrFun hz i') j
      have hz2 : Fw P p i' j = 0 := by
        by_contra hne
        apply hnot
        rw [Sym2.eq_swap]
        exact Fw_support P p i' j hne
      rw [Fw, Matrix.sub_apply, Mx_rl, hz2] at h0
      simp at h0
    · exact absurd h (by simp [supportGraph, supportRel])

end CycAux

open CycAux in
theorem cycle_pert {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ)
    (hcyc : ¬ (supportGraph P).IsAcyclic) :
    ∃ E : Matrix (Fin n) (Fin m) ℝ, E ≠ 0 ∧
      (∀ i, ∑ j, E i j = 0) ∧ (∀ j, ∑ i, E i j = 0) ∧
      (∀ i j, E i j ≠ 0 → 0 < P i j) := by
  unfold SimpleGraph.IsAcyclic at hcyc
  push Not at hcyc
  obtain ⟨v, c, hc⟩ := hcyc
  have hev : Even c.length := (even_closed P c).2 rfl
  refine ⟨Fw P c, Fw_ne_zero P c hc, ?_, ?_, ?_⟩
  · intro i
    have := Sx_Fw P (Sum.inl i) c
    simp only [Sx, Sum.elim_inl, hev.neg_one_pow] at this
    rw [this]; ring
  · intro j
    have := Sx_Fw P (Sum.inr j) c
    simp only [Sx, Sum.elim_inr, hev.neg_one_pow] at this
    rw [this]; ring
  · intro i j h
    have h1 := Fw_support P c i j h
    have h2 := c.edges_subset_edgeSet h1
    rw [SimpleGraph.mem_edgeSet] at h2
    exact h2


theorem feas {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P E : Matrix (Fin n) (Fin m) ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (hP : P ∈ CompOT.Assignment.couplings a b)
    (hrow : ∀ i, ∑ j, E i j = 0) (hcol : ∀ j, ∑ i, E i j = 0)
    (hsupp : ∀ i j, E i j ≠ 0 → 0 < P i j) :
    ∃ t : ℝ, 0 < t ∧ P + t • E ∈ CompOT.Assignment.couplings a b ∧
      P - t • E ∈ CompOT.Assignment.couplings a b := by
  obtain ⟨hP0, hPr, hPc⟩ := hP
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j, t * |E i j| ≤ P i j := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    by_cases h : E i j = 0
    · simp [h, hP0 i j]
    · have habs : 0 < |E i j| := abs_pos.2 h
      have hlt : (0 : ℝ) < P i j / |E i j| := div_pos (hsupp i j h) habs
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t < P i j / |E i j| := Iio_mem_nhds hlt
      filter_upwards [nhdsWithin_le_nhds this] with t ht
      rw [lt_div_iff₀ habs] at ht
      exact ht.le
  obtain ⟨t, ht, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have htp : 0 < t := htpos
  refine ⟨t, htp, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro i j
    have := ht i j
    have h2 := neg_abs_le (E i j)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2 htp.le]
  · intro i
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hrow, hPr, mul_zero, add_zero]
  · intro j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hcol, hPc, mul_zero, add_zero]
  · intro i j
    have := ht i j
    have h2 := le_abs_self (E i j)
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2 htp.le]
  · intro i
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hrow, hPr, mul_zero, sub_zero]
  · intro j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hcol, hPc, mul_zero, sub_zero]


theorem edges_nz {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) :
    Nat.card (supportGraph P).edgeSet = (nonzeroEntries P).card := by
  classical
  set f : Fin n × Fin m → Sym2 (Fin n ⊕ Fin m) := fun p => s(Sum.inl p.1, Sum.inr p.2) with hf
  have hinj : Function.Injective f := by
    intro p q h
    simp only [hf, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
    · simp at h1
  have hset : (supportGraph P).edgeSet = f '' {p : Fin n × Fin m | 0 < P p.1 p.2} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · intro h
        rcases a with i | j <;> rcases b with i' | j'
        · exact absurd h (by simp [supportGraph, supportRel])
        · exact ⟨(i, j'), h, rfl⟩
        · refine ⟨(i', j), h, ?_⟩
          simp [hf, Sym2.eq_swap]
        · exact absurd h (by simp [supportGraph, supportRel])
      · rintro ⟨⟨i, j⟩, hij, h⟩
        simp only [hf, Sym2.eq_iff] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2; exact hij
        · subst h1; subst h2
          exact (show (supportGraph P).Adj (Sum.inl i) (Sum.inr j) from hij).symm
  have hA : {p : Fin n × Fin m | 0 < P p.1 p.2} = ↑(nonzeroEntries P) := by
    ext p
    simp only [Set.mem_setOf_eq, nonzeroEntries, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.ne'
    · intro h; exact lt_of_le_of_ne (hP _ _) (Ne.symm h)
  rw [hset, Nat.card_image_of_injective hinj _, hA, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (hP : IsExtremal (CompOT.Assignment.couplings a b) P) :
    (supportGraph P).IsAcyclic ∧ (nonzeroEntries P).card ≤ n + m - 1 := by
  classical
  obtain ⟨hPmem, hext⟩ := hP
  have hacyc : (supportGraph P).IsAcyclic := by
    by_contra hcyc
    obtain ⟨E, hE0, hrow, hcol, hsupp⟩ := cycle_pert P hcyc
    obtain ⟨t, ht, hQ, hR⟩ := feas a b P E ha hb hPmem hrow hcol hsupp
    have hmid : P = (1 / 2 : ℝ) • ((P + t • E) + (P - t • E)) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    obtain ⟨h1, _⟩ := hext _ hQ _ hR hmid
    apply hE0
    have h2 : t • E = 0 := by
      have : P + t • E = P + 0 := by rw [add_zero]; exact h1.symm
      exact add_left_cancel this
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h ht.ne'
    · exact h
  refine ⟨hacyc, ?_⟩
  have hPnn : ∀ i j, 0 ≤ P i j := hPmem.1
  have hcard := edges_nz P hPnn
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have := ha.2
      simp at this
    · exact h
  have hne : Nonempty (Fin n ⊕ Fin m) := ⟨Sum.inl ⟨0, hn⟩⟩
  have hconn : (⊤ : SimpleGraph (Fin n ⊕ Fin m)).Connected := SimpleGraph.connected_top
  obtain ⟨F, hGF, _, hF⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic (le_top : supportGraph P ≤ ⊤) hacyc
  have h1 := hF.card_edgeFinset
  have h2 : Nat.card (supportGraph P).edgeSet ≤ Nat.card F.edgeSet :=
    Nat.card_mono (Set.toFinite _) (SimpleGraph.edgeSet_mono hGF)
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h2
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h2
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hcard
  simp only [Fintype.card_sum, Fintype.card_fin] at h1
  omega
