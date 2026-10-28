-- Prove2me | solution 1 for GCT.dc_le_two_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:00:54.608862+00:00
-- url     : https://prove2.me/submissions/03fbd54c-b17a-4886-8125-e9123adf43b4

import Definitions.Def_GCT_determinantal_complexity

namespace S216GCT
open MvPolynomial Finset

noncomputable section

lemma det_tri {ι α R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [LinearOrder α]
    (M : Matrix ι ι R) (b : ι → α) (hb : Function.Injective b)
    (h : ∀ i j, b j < b i → M i j = 0) : M.det = ∏ i, M i i := by
  let _ : LinearOrder ι := LinearOrder.lift' b hb
  convert Matrix.det_of_isUpperTriangular (M := M) (fun i j hij => h i j hij)

abbrev R (m : ℕ) := MvPolynomial (GCT.PadVars m) ℂ

def xx (m r : ℕ) (j : Fin m) : R m := if h : r < m then X (some (⟨r, h⟩, j)) else 0

lemma xx_hom (m r : ℕ) (j : Fin m) : (xx m r j).IsHomogeneous 1 := by
  unfold xx; split_ifs
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_zero _ _ _

def P (m : ℕ) : ℕ → Finset (Fin m) → R m
  | 0, T => if T = ∅ then 1 else 0
  | k+1, T => ∑ j ∈ T, P m k (T.erase j) * xx m k j

lemma image_snoc {m k : ℕ} (g : Fin k → Fin m) (j : Fin m) :
    (univ.image ((Fin.snocEquiv fun _ => Fin m) (j, g))) = insert j (univ.image g) := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_insert, Fin.exists_fin_succ', Fin.snocEquiv_apply,
    Fin.snoc_castSucc, Fin.snoc_last]
  tauto

lemma key {m k : ℕ} (T : Finset (Fin m)) (g : Fin k → Fin m) (j : Fin m) :
    (insert j (univ.image g) = T ∧ T.card = k + 1) ↔
      (j ∈ T ∧ (univ.image g = T.erase j ∧ (T.erase j).card = k)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hj : j ∈ T := h1 ▸ mem_insert_self _ _
    have hc : (univ.image g).card ≤ k := card_image_le.trans (by simp)
    have hnot : j ∉ univ.image g := by
      intro hm; rw [insert_eq_of_mem hm] at h1; rw [h1] at hc; omega
    refine ⟨hj, ?_, ?_⟩
    · rw [← h1, erase_insert hnot]
    · rw [card_erase_of_mem hj, h2]; rfl
  · rintro ⟨hj, h1, h2⟩
    refine ⟨by rw [h1, insert_erase hj], ?_⟩
    rw [card_erase_of_mem hj] at h2
    have := card_pos.2 ⟨j, hj⟩
    omega

lemma P_closed (m k : ℕ) (T : Finset (Fin m)) :
    P m k T = ∑ f : Fin k → Fin m,
      if univ.image f = T ∧ T.card = k then ∏ r : Fin k, xx m r (f r) else 0 := by
  induction k generalizing T with
  | zero =>
    simp [P, eq_comm]
  | succ k ih =>
    rw [P, ← (Fin.snocEquiv (fun _ => Fin m)).sum_comp, Fintype.sum_prod_type]
    simp only [image_snoc, key]
    simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last]
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ T)]
    rw [Finset.sum_eq_zero (s := univ.filter (fun j => j ∉ T)) (by
      intro j hj; rw [mem_filter] at hj
      exact Finset.sum_eq_zero fun g _ => if_neg (fun h => hj.2 h.1)), add_zero]
    rw [Finset.filter_mem_eq_inter, univ_inter]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [hj, true_and]
    split_ifs <;> simp

lemma P_univ (m : ℕ) : P m m univ = GCT.permPolyPad m := by
  rw [P_closed, GCT.permPolyPad, ← Matrix.permanent_transpose, Matrix.permanent]
  simp only [Matrix.transpose_apply, Matrix.of_apply, card_univ, Fintype.card_fin, and_true]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun σ _ => ⇑σ)
    (fun f hf => Equiv.ofBijective f (by
      have hs : Function.Surjective f := by
        intro y
        have : y ∈ univ.image f := by rw [(mem_filter.1 hf).2]; exact mem_univ _
        simpa using this
      exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩)) ?_ ?_ ?_ ?_ ?_
  · intro σ _
    simp only [mem_filter, mem_univ, true_and]
    ext y; simp only [mem_image, mem_univ, true_and, iff_true]; exact σ.surjective y
  · intro f hf; exact mem_univ _
  · intro σ _; ext; rfl
  · intro f hf; rfl
  · intro σ _
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [xx]

abbrev ι (m : ℕ) := {S : Finset (Fin m) // S ≠ univ}

lemma card_ι (m : ℕ) : Fintype.card (ι m) = 2 ^ m - 1 := by
  simp [Fintype.card_finset]

def emp (m : ℕ) : ι (m+1) := ⟨∅, fun h => by
  have := congrArg ((0 : Fin (m+1)) ∈ ·) h; simp at this⟩

lemma sum_sub {m : ℕ} {β : Type*} [AddCommMonoid β] (A : Finset (Fin m)) (hA : A ≠ univ)
    (f : ι m → β) : ∑ S : ι m, (if S.1 = A then f S else 0) = f ⟨A, hA⟩ := by
  rw [Fintype.sum_eq_single ⟨A, hA⟩]
  · simp
  · intro S hS; rw [if_neg]; exact fun h => hS (Subtype.ext h)

lemma erase_ne {m : ℕ} (T : Finset (Fin m)) (hT : T ≠ univ) (j : Fin m) : T.erase j ≠ univ :=
  fun h => hT (eq_univ_of_forall fun x => erase_subset j T (h ▸ mem_univ x))

def M (m : ℕ) : Matrix (ι (m+1)) (ι (m+1)) (R (m+1)) := Matrix.of fun S T =>
  if T.1 = ∅ then ∑ j : Fin (m+1), (if S.1 = univ.erase j then xx (m+1) m j else 0)
  else (if S = T then -X none else 0) +
    ∑ j ∈ T.1, (if S.1 = T.1.erase j then xx (m+1) S.1.card j else 0)

lemma M_hom (m : ℕ) (S T : ι (m+1)) : (M m S T).IsHomogeneous 1 := by
  simp only [M, Matrix.of_apply]
  have h0 : IsHomogeneous (0 : R (m+1)) 1 := isHomogeneous_zero _ _ _
  by_cases hT : T.1 = ∅
  · rw [if_pos hT]; refine IsHomogeneous.sum _ _ _ fun j _ => ?_
    split_ifs
    exacts [xx_hom _ _ _, h0]
  · rw [if_neg hT]; refine IsHomogeneous.add ?_ (IsHomogeneous.sum _ _ _ fun j _ => ?_)
    · split_ifs
      exacts [(isHomogeneous_X _ _).neg, h0]
    · split_ifs
      exacts [xx_hom _ _ _, h0]

def y (m : ℕ) (S : ι (m+1)) : R (m+1) := X none ^ (m - S.1.card) * P (m+1) S.1.card S.1

def Q (m : ℕ) : Matrix (ι (m+1)) (ι (m+1)) (R (m+1)) := Matrix.of fun S T =>
  if S.1 = ∅ then y m T else if S = T then 1 else 0

lemma QM_row (m : ℕ) (S T : ι (m+1)) (hS : S.1 ≠ ∅) : (Q m * M m) S T = M m S T := by
  simp [Matrix.mul_apply, Q, hS]

lemma QM_zero (m : ℕ) (S T : ι (m+1)) (hS : S.1 = ∅) :
    (Q m * M m) S T = ∑ U, y m U * M m U T := by
  simp [Matrix.mul_apply, Q, hS]

lemma card_lt {m : ℕ} (S : ι m) : S.1.card < m := by
  have := (Finset.card_lt_iff_ne_univ _).2 S.2; simpa using this

lemma row_kill (m : ℕ) (T : ι (m+1)) (hT : T.1 ≠ ∅) : ∑ U, y m U * M m U T = 0 := by
  simp only [M, Matrix.of_apply, if_neg hT, mul_add, sum_add_distrib, mul_ite, mul_zero,
    Finset.mul_sum]
  rw [Finset.sum_ite_eq', if_pos (mem_univ _), Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => sum_sub (T.1.erase j) (erase_ne _ T.2 j)
    (fun U => y m U * xx (m+1) U.1.card j)]
  obtain ⟨c, hc⟩ : ∃ c, T.1.card = c + 1 :=
    ⟨T.1.card - 1, by have := card_pos.2 (nonempty_iff_ne_empty.2 hT); omega⟩
  have hcm := card_lt T
  have h2 : ∀ j ∈ T.1, y m ⟨T.1.erase j, erase_ne _ T.2 j⟩ * xx (m+1) (T.1.erase j).card j =
      X none ^ (m - c) * (P (m+1) c (T.1.erase j) * xx (m+1) c j) := by
    intro j hj
    simp only [y, card_erase_of_mem hj, hc, Nat.add_sub_cancel]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  simp only [y, hc, P]
  have : m - c = (m - (c+1)) + 1 := by omega
  rw [this, pow_succ]; ring

lemma corner (m : ℕ) : ∑ U, y m U * M m U (emp m) = P (m+1) (m+1) univ := by
  simp only [M, Matrix.of_apply, emp, ↓reduceIte, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => sum_sub (univ.erase j) (erase_ne _ (emp m).2 j |> fun _ =>
    (Finset.erase_ssubset (mem_univ j)).ne) (fun U => y m U * xx (m+1) m j)]
  rw [P]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [y, card_erase_of_mem]

def bQ (m : ℕ) (S : ι (m+1)) : ℕ ×ₗ Fin (Fintype.card (ι (m+1))) :=
  toLex ((if S.1 = ∅ then 0 else 1 : ℕ), Fintype.equivFin _ S)

def bM (m : ℕ) (S : ι (m+1)) : ℕ ×ₗ Fin (Fintype.card (ι (m+1))) :=
  toLex ((if S.1 = ∅ then m+1 else S.1.card : ℕ), Fintype.equivFin _ S)

lemma inj_aux {m : ℕ} (f : ι (m+1) → ℕ) :
    Function.Injective (fun S => toLex (f S, Fintype.equivFin (ι (m+1)) S)) := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  exact (Fintype.equivFin _).injective this

lemma detQ (m : ℕ) : (Q m).det = X none ^ m := by
  rw [det_tri (Q m) (bQ m) (inj_aux _)]
  · rw [Fintype.prod_eq_mul_prod_compl (emp m)]
    rw [Finset.prod_eq_one]
    · simp [Q, emp, y, P]
    · intro i hi
      have : i.1 ≠ ∅ := fun h => by
        simp only [mem_compl, mem_singleton] at hi; exact hi (Subtype.ext h)
      simp [Q, this]
  · intro i j hlt
    simp only [Q, Matrix.of_apply]
    split_ifs with hi hij
    · exfalso
      simp only [bQ, Prod.Lex.toLex_lt_toLex, if_pos hi] at hlt
      rcases hlt with h | ⟨h1, h2⟩
      · omega
      · have hj : j.1 = ∅ := by by_contra hj; rw [if_neg hj] at h1; omega
        have : i = j := Subtype.ext (hi.trans hj.symm)
        subst this; exact lt_irrefl _ h2
    · subst hij; exact absurd hlt (lt_irrefl _)
    · rfl

lemma even_aux (m : ℕ) : Even (2 ^ (m+1) - 1 - 1) := by
  refine ⟨2 ^ m - 1, ?_⟩
  have := Nat.one_le_two_pow (n := m)
  rw [pow_succ]; omega

lemma detQM (m : ℕ) : (Q m * M m).det = P (m+1) (m+1) univ * X none ^ (2 ^ (m+1) - 2) := by
  rw [det_tri (Q m * M m) (bM m) (inj_aux _)]
  · rw [Fintype.prod_eq_mul_prod_compl (emp m)]
    rw [QM_zero _ _ _ rfl, corner]
    congr 1
    rw [Finset.prod_congr rfl (g := fun _ => -X none), prod_const, card_compl, card_singleton,
      card_ι, (even_aux m).neg_pow]
    · rfl
    · intro i hi
      have hi' : i.1 ≠ ∅ := fun h => by
        simp only [mem_compl, mem_singleton] at hi; exact hi (Subtype.ext h)
      rw [QM_row _ _ _ hi']
      simp only [M, Matrix.of_apply, if_neg hi', ↓reduceIte]
      rw [Finset.sum_eq_zero, add_zero]
      intro k hk
      rw [if_neg]
      intro h
      exact (Finset.erase_eq_self.1 h.symm) hk
  · intro i j hlt
    have hci := card_lt i
    have hcj := card_lt j
    by_cases hi : i.1 = ∅
    · rw [QM_zero _ _ _ hi]
      by_cases hj : j.1 = ∅
      · have : i = j := Subtype.ext (hi.trans hj.symm)
        subst this; exact absurd hlt (lt_irrefl _)
      · exact row_kill m j hj
    · rw [QM_row _ _ _ hi]
      simp only [M, Matrix.of_apply]
      split_ifs with hj hij
      · exfalso
        simp only [bM, Prod.Lex.toLex_lt_toLex, if_pos hj, if_neg hi] at hlt
        omega
      · subst hij; exact absurd hlt (lt_irrefl _)
      · rw [zero_add]
        refine Finset.sum_eq_zero fun k hk => if_neg fun h => ?_
        have hc : i.1.card + 1 = j.1.card := by
          rw [h, card_erase_of_mem hk]; have := card_pos.2 ⟨k, hk⟩; omega
        simp only [bM, Prod.Lex.toLex_lt_toLex, if_neg hj, if_neg hi] at hlt
        omega

lemma mem (m : ℕ) : m ≤ 2 ^ m - 1 ∧ GCT.HasLinearDetRep (2 ^ m - 1) (GCT.paddedPerm m (2 ^ m - 1)) := by
  rcases m with _ | m
  · show 0 ≤ 0 ∧ GCT.HasLinearDetRep 0 (GCT.paddedPerm 0 0)
    refine ⟨le_rfl, 0, fun i => i.elim0, ?_⟩
    simp [GCT.paddedPerm, GCT.permPolyPad, Matrix.permanent_isEmpty]
  · have hlt : m + 1 < 2 ^ (m+1) := Nat.lt_two_pow_self
    refine ⟨by omega, ?_⟩
    let e : ι (m+1) ≃ Fin (2 ^ (m+1) - 1) := Fintype.equivFinOfCardEq (card_ι _)
    refine ⟨Matrix.reindex e e (M m), fun i j => M_hom _ _ _, ?_⟩
    rw [Matrix.det_reindex_self]
    have h := Matrix.det_mul (Q m) (M m)
    rw [detQM, detQ] at h
    refine mul_left_cancel₀ (pow_ne_zero m (X_ne_zero (none : GCT.PadVars (m+1)))) ?_
    rw [← h, GCT.paddedPerm, P_univ]
    have : 2 ^ (m+1) - 2 = m + (2 ^ (m+1) - 1 - (m+1)) := by omega
    rw [this, pow_add]; ring

end

end S216GCT

theorem solution (m : ℕ) : GCT.dc m ≤ 2 ^ m - 1 := Nat.sInf_le (S216GCT.mem m)
