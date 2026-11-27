-- Prove2me | solution 1 for BarelyTestable.LowerBound.repair_propagation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:32:03.734158+00:00
-- url     : https://prove2.me/submissions/d2db0419-030e-4c66-b74d-cf960220a435

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_repair_propagation

variable {m : ℕ}

/-- Blockwise comparability: in every block one set contains the other. -/
def Comparable (A B : HalfSet m) : Prop :=
  ∀ i : Fin m, (∀ k, (i, k) ∈ A → (i, k) ∈ B) ∨ (∀ k, (i, k) ∈ B → (i, k) ∈ A)

lemma block_union (A B : HalfSet m) (i : Fin m) :
    block (A ∪ B) i = block A i ∪ block B i := by
  ext k; simp [block]

lemma block_inter (A B : HalfSet m) (i : Fin m) :
    block (A ∩ B) i = block A i ∩ block B i := by
  ext k; simp [block]

lemma blocksum_mod (ψ : Fin m → Finset (Fin m) → ℝ) (A B : HalfSet m)
    (h : Comparable A B) :
    (∑ i, ψ i (block (A ∪ B) i)) + (∑ i, ψ i (block (A ∩ B) i)) =
      (∑ i, ψ i (block A i)) + (∑ i, ψ i (block B i)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [block_union, block_inter]
  rcases h i with h | h
  · have hs : block A i ⊆ block B i := by
      intro k hk; simp [block] at hk ⊢; exact h k hk
    rw [Finset.union_eq_right.mpr hs, Finset.inter_eq_left.mpr hs]; ring
  · have hs : block B i ⊆ block A i := by
      intro k hk; simp [block] at hk ⊢; exact h k hk
    rw [Finset.union_eq_left.mpr hs, Finset.inter_eq_right.mpr hs]

lemma baseA_mod (A B Y : HalfSet m) (h : Comparable A B) :
    baseA (A ∪ B) Y + baseA (A ∩ B) Y = baseA A Y + baseA B Y := by
  have := blocksum_mod (fun _ s => ((s.card : ℝ) + Y.card) ^ 2) A B h
  simp only [baseA]
  linarith

lemma bitDistance_cast (v w : Bits m) :
    (bitDistance v w : ℝ) = ∑ i, if v i ≠ w i then (1:ℝ) else 0 := by
  simp [bitDistance, Finset.card_filter]

lemma bitL_mod (w : Bits m) (A B : HalfSet m) (h : Comparable A B) :
    (bitDistance (parity (A ∪ B)) w : ℝ) + bitDistance (parity (A ∩ B)) w =
      bitDistance (parity A) w + bitDistance (parity B) w := by
  have := blocksum_mod (fun i s => if decide (s.card % 2 = 1) ≠ w i then (1:ℝ) else 0) A B h
  simp only [bitDistance_cast, parity]
  exact this

lemma bitR_mod (w : Bits m) (A B : HalfSet m) (h : Comparable A B) :
    (bitDistance w (parity (A ∪ B)) : ℝ) + bitDistance w (parity (A ∩ B)) =
      bitDistance w (parity A) + bitDistance w (parity B) := by
  have := blocksum_mod (fun i s => if w i ≠ decide (s.card % 2 = 1) then (1:ℝ) else 0) A B h
  simp only [bitDistance_cast, parity]
  exact this

/-- The coordinate set used by `residual`. -/
def Sset (side : Bool) (fixed : HalfSet m) (τ : Bool) (Z : HalfSet m) : Finset (Coord m) :=
  let X := if side then Z else fixed
  let Y := if side then fixed else Z
  let a := if side then false else true
  let b := τ
  (X.image (fun x => Sum.inr (Sum.inl x) : Half m → Coord m)) ∪
    (Y.image (fun y => Sum.inr (Sum.inr y) : Half m → Coord m)) ∪
    (if a then {actionA} else ∅) ∪ (if b then {actionB} else ∅)

/-- The slice term used by `residual`. -/
noncomputable def sl (r : Sample m) (side : Bool) (fixed : HalfSet m) (τ : Bool)
    (Z : HalfSet m) : ℝ :=
  let X := if side then Z else fixed
  let Y := if side then fixed else Z
  let a := if side then false else true
  let b := τ
  slice r false X Y a b

lemma residual_eq (r : Sample m) (G : Oracle (Coord m)) (side : Bool) (fixed : HalfSet m)
    (τ : Bool) (Z : HalfSet m) :
    residual r G side fixed τ Z = G (Sset side fixed τ Z) - sl r side fixed τ Z := rfl

lemma Sset_union (side : Bool) (fixed : HalfSet m) (τ : Bool) (A B : HalfSet m) :
    Sset side fixed τ (A ∪ B) = Sset side fixed τ A ∪ Sset side fixed τ B := by
  cases side <;> ext x <;> rcases x with b | x | y <;> simp [Sset] <;> tauto

lemma Sset_inter (side : Bool) (fixed : HalfSet m) (τ : Bool) (A B : HalfSet m) :
    Sset side fixed τ (A ∩ B) = Sset side fixed τ A ∩ Sset side fixed τ B := by
  cases side <;> ext x <;> rcases x with b | x | y <;> simp [Sset] <;> tauto

lemma sl_mod (r : Sample m) (side : Bool) (fixed : HalfSet m) (τ : Bool) (A B : HalfSet m)
    (h : Comparable A B) :
    sl r side fixed τ (A ∪ B) + sl r side fixed τ (A ∩ B) =
      sl r side fixed τ A + sl r side fixed τ B := by
  have hc : ((A ∪ B).card : ℝ) + (A ∩ B).card = A.card + B.card := by
    exact_mod_cast Finset.card_union_add_card_inter A B
  have h1 := baseA_mod A B fixed h
  cases side <;> cases τ <;> simp [sl, slice, baseB]
  · linear_combination h1 - (m:ℝ)^4 * hc
  · linear_combination h1 - 2 * (m:ℝ)^4 * hc - bitR_mod (r.1 fixed) A B h
  · linarith
  · linear_combination h1 - (m:ℝ)^4 * hc + bitL_mod (r.2.1 fixed) A B h

theorem pair (r : Sample m) (G : Oracle (Coord m)) (hG : Submodular G) (side : Bool)
    (fixed : HalfSet m) (τ : Bool) (A B : HalfSet m) (h : Comparable A B) :
    residual r G side fixed τ (A ∪ B) + residual r G side fixed τ (A ∩ B) ≤
      residual r G side fixed τ A + residual r G side fixed τ B := by
  simp only [residual_eq]
  have hs := sl_mod r side fixed τ A B h
  have hg := hG (Sset side fixed τ A) (Sset side fixed τ B)
  rw [← Sset_union, ← Sset_inter] at hg
  linarith


/-! ### Counting over selectors -/

/-- The points of a selector in the blocks of `R`. -/
def img (R : Finset (Fin m)) (γ : Selector m) : HalfSet m :=
  R.image (fun i => ((i, γ i) : Half m))

lemma card_selector : (Fintype.card (Selector m) : ℝ) = (m : ℝ) ^ m := by
  simp

lemma slice_card (j : Fin m) (Q : Selector m → Prop) [DecidablePred Q]
    (hQ : ∀ γ w, Q (Function.update γ j w) ↔ Q γ) (v : Fin m) :
    m * (Finset.univ.filter (fun γ : Selector m => γ j = v ∧ Q γ)).card =
      (Finset.univ.filter Q).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun γ : Selector m => γ j)
    (s := Finset.univ.filter Q) (t := Finset.univ) (by intro x _; simp)]
  have : ∀ w ∈ (Finset.univ : Finset (Fin m)),
      ((Finset.univ.filter Q).filter (fun γ : Selector m => γ j = w)).card =
      (Finset.univ.filter (fun γ : Selector m => γ j = v ∧ Q γ)).card := by
    intro w _
    apply Finset.card_nbij' (fun γ => Function.update γ j v) (fun γ => Function.update γ j w)
    · intro γ hγ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact ⟨by simp, (hQ γ v).2 hγ.1⟩
    · intro γ hγ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact ⟨(hQ γ w).2 hγ.2, by simp⟩
    · intro γ hγ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hγ
      show Function.update (Function.update γ j v) j w = γ
      rw [Function.update_idem, ← hγ.2, Function.update_eq_self]
    · intro γ hγ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
      show Function.update (Function.update γ j w) j v = γ
      rw [Function.update_idem, ← hγ.1, Function.update_eq_self]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

lemma arith (k m M x : ℝ) (hm : 0 ≤ m) (hk : m / 4 ≤ k) (hx1 : M / 4 ≤ x)
    (hx2 : x ≤ M) : m * (M / 4) ≤ k * x + (m - k) * min (M / 4) (M - x) := by
  have hk0 : 0 ≤ k := by linarith
  rcases le_total (M / 4) (M - x) with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg hk0 (sub_nonneg.2 hx1)]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.2 hk) (by linarith : (0:ℝ) ≤ 4 * x - 3 * M),
      mul_nonneg hk0 (sub_nonneg.2 hx2)]

lemma img_univ (γ : Selector m) : img Finset.univ γ = selected γ := rfl

lemma comparable_xor (X : HalfSet m) (γ : Selector m) :
    Comparable X (xorSet X (selected γ)) := by
  intro i
  by_cases h : (i, γ i) ∈ X
  · right
    intro k hk
    simp only [xorSet, selected, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
      Finset.mem_univ, true_and, Prod.mk.injEq] at hk
    rcases hk with ⟨hk, _⟩ | ⟨⟨a, rfl, rfl⟩, _⟩
    · exact hk
    · exact h
  · left
    intro k hk
    simp only [xorSet, selected, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
      Finset.mem_univ, true_and, Prod.mk.injEq]
    left
    refine ⟨hk, ?_⟩
    rintro ⟨a, rfl, rfl⟩
    exact h hk

lemma xor_block_card (X : HalfSet m) (γ : Selector m) (i : Fin m) :
    ((block X i).card : ℝ) - 1 ≤ (block (xorSet X (selected γ)) i).card := by
  have hsub : (block X i).erase (γ i) ⊆ block (xorSet X (selected γ)) i := by
    intro k hk
    rw [Finset.mem_erase] at hk
    simp only [block, Finset.mem_filter, Finset.mem_univ, true_and, xorSet, selected,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_image, Prod.mk.injEq] at hk ⊢
    left
    refine ⟨hk.2, ?_⟩
    rintro ⟨a, rfl, rfl⟩
    exact hk.1 rfl
  have h1 := Finset.pred_card_le_card_erase (s := block X i) (a := γ i)
  have h2 := Finset.card_le_card hsub
  have h3 : ((block X i).card : ℝ) - 1 ≤ (((block X i).card - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (block X i).card with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub h]; simp
  have h4 : ((((block X i).card - 1 : ℕ)) : ℝ) ≤ (block (xorSet X (selected γ)) i).card := by
    exact_mod_cast h1.trans h2
  linarith

section positive

variable (g : HalfSet m → ℝ)
  (hpair : ∀ A B : HalfSet m, Comparable A B → g (A ∪ B) + g (A ∩ B) ≤ g A + g B)
include hpair

/-- Counting form of Claim 3.15 on the cube of free blocks `R`. -/
theorem positive (R : Finset (Fin m)) : ∀ Z : HalfSet m, 0 < g Z →
    (∀ i ∈ R, (m : ℝ) / 4 ≤ (block Z i).card) →
    (m : ℝ) ^ m / 4 ≤ (Finset.univ.filter (fun γ : Selector m => g (Z ∪ img R γ) ≠ 0)).card := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Z hZ _
    have : (Finset.univ.filter (fun γ : Selector m => g (Z ∪ img ∅ γ) ≠ 0)) = Finset.univ := by
      ext γ; simp [img, hZ.ne']
    rw [this, Finset.card_univ, card_selector]
    have : (0:ℝ) ≤ (m : ℝ) ^ m := by positivity
    linarith
  | @insert j R hj ih =>
    intro Z hZ hb
    have hmpos : 0 < m := j.pos
    set M : ℝ := (m : ℝ) ^ m with hM
    let cnt : HalfSet m → ℝ := fun Z' =>
      ((Finset.univ.filter (fun γ : Selector m => g (Z' ∪ img R γ) ≠ 0)).card : ℝ)
    have hcntM : ∀ Z', cnt Z' ≤ M := by
      intro Z'
      simp only [cnt]
      rw [hM, ← card_selector]
      exact_mod_cast Finset.card_le_univ _
    have hx := ih Z hZ (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    -- img does not depend on coordinate j
    have himg : ∀ γ w, img R (Function.update γ j w) = img R γ := by
      intro γ w
      apply Finset.image_congr
      intro i hi
      have : i ≠ j := fun h => hj (h ▸ hi)
      simp [Function.update_of_ne this]
    -- decomposition
    have hdec : (m : ℝ) * ((Finset.univ.filter
        (fun γ : Selector m => g (Z ∪ img (insert j R) γ) ≠ 0)).card : ℝ) =
        ∑ v : Fin m, cnt (insert (j, v) Z) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun γ : Selector m => γ j)
        (t := Finset.univ) (by intro x _; simp)]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      have hset : ((Finset.univ.filter
          (fun γ : Selector m => g (Z ∪ img (insert j R) γ) ≠ 0)).filter
            (fun γ : Selector m => γ j = v)) =
          Finset.univ.filter (fun γ : Selector m =>
            γ j = v ∧ g (insert (j, v) Z ∪ img R γ) ≠ 0) := by
        ext γ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h2, ?_⟩
          have : Z ∪ img (insert j R) γ = insert (j, v) Z ∪ img R γ := by
            simp [img, Finset.image_insert, h2, Finset.insert_union, Finset.union_insert]
          rwa [this] at h1
        · rintro ⟨h2, h1⟩
          refine ⟨?_, h2⟩
          have : Z ∪ img (insert j R) γ = insert (j, v) Z ∪ img R γ := by
            simp [img, Finset.image_insert, h2, Finset.insert_union, Finset.union_insert]
          rwa [this]
      rw [hset]
      have := slice_card j (fun γ : Selector m => g (insert (j, v) Z ∪ img R γ) ≠ 0)
        (by intro γ w; simp only [himg]) v
      simp only [cnt]
      exact_mod_cast this
    -- per-term bounds
    have hin : ∀ v ∈ block Z j, cnt (insert (j, v) Z) = cnt Z := by
      intro v hv
      have : (j, v) ∈ Z := by simpa [block] using hv
      simp only [cnt, Finset.insert_eq_of_mem this]
    have hout : ∀ v ∈ (block Z j)ᶜ, min (M / 4) (M - cnt Z) ≤ cnt (insert (j, v) Z) := by
      intro v hv
      have hvZ : (j, v) ∉ Z := by simpa [block] using hv
      by_cases hpos : 0 < g (insert (j, v) Z)
      · refine (min_le_left _ _).trans ?_
        apply ih _ hpos
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        have : block (insert (j, v) Z) i = block Z i := by
          ext k; simp [block, hij]
        rw [this]; exact hb i (Finset.mem_insert_of_mem hi)
      · refine (min_le_right _ _).trans ?_
        have hcover : ∀ γ : Selector m,
            g (Z ∪ img R γ) ≠ 0 ∨ g (insert (j, v) Z ∪ img R γ) ≠ 0 := by
          intro γ
          by_contra hcon
          push Not at hcon
          have hnot : (j, v) ∉ img R γ := by
            simp only [img, Finset.mem_image, not_exists, not_and]
            intro i hi he
            simp only [Prod.mk.injEq] at he
            exact hj (he.1 ▸ hi)
          have hc : Comparable (insert (j, v) Z) (Z ∪ img R γ) := by
            intro i
            by_cases hij : i = j
            · subst hij
              right
              intro k hk
              rcases Finset.mem_union.mp hk with hk | hk
              · exact Finset.mem_insert_of_mem hk
              · exfalso
                simp only [img, Finset.mem_image, Prod.mk.injEq] at hk
                obtain ⟨a, ha, rfl, -⟩ := hk
                exact hj ha
            · left
              intro k hk
              rcases Finset.mem_insert.mp hk with hk | hk
              · exact absurd (congrArg Prod.fst hk) hij
              · exact Finset.mem_union_left _ hk
          have h := hpair _ _ hc
          have hu : insert (j, v) Z ∪ (Z ∪ img R γ) = insert (j, v) Z ∪ img R γ := by
            ext q; simp only [Finset.mem_union, Finset.mem_insert]; tauto
          have hi : insert (j, v) Z ∩ (Z ∪ img R γ) = Z := by
            ext q
            simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | h1, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hvZ
                · exact absurd h2 hnot
              · exact h1
            · intro hq; exact ⟨Or.inr hq, Or.inl hq⟩
          rw [hu, hi, hcon.1, hcon.2] at h
          linarith
        have hU : (Finset.univ.filter (fun γ : Selector m => g (Z ∪ img R γ) ≠ 0)) ∪
            (Finset.univ.filter (fun γ : Selector m => g (insert (j, v) Z ∪ img R γ) ≠ 0)) =
            Finset.univ := by
          rw [← Finset.filter_or]
          exact Finset.filter_true_of_mem (fun γ _ => hcover γ)
        have hle := Finset.card_union_le
          (Finset.univ.filter (fun γ : Selector m => g (Z ∪ img R γ) ≠ 0))
          (Finset.univ.filter (fun γ : Selector m => g (insert (j, v) Z ∪ img R γ) ≠ 0))
        rw [hU, Finset.card_univ] at hle
        have hle' : (Fintype.card (Selector m) : ℝ) ≤ cnt Z + cnt (insert (j, v) Z) := by
          simp only [cnt]
          exact_mod_cast hle
        rw [card_selector] at hle'
        linarith
    -- sum up
    have hsum : (block Z j).card * cnt Z + ((m : ℝ) - (block Z j).card) *
        min (M / 4) (M - cnt Z) ≤ ∑ v : Fin m, cnt (insert (j, v) Z) := by
      rw [← Finset.sum_add_sum_compl (block Z j)]
      have h1 : ∑ v ∈ block Z j, cnt (insert (j, v) Z) = (block Z j).card * cnt Z := by
        rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
      have h2 : ((block Z j)ᶜ.card : ℝ) * min (M / 4) (M - cnt Z) ≤
          ∑ v ∈ (block Z j)ᶜ, cnt (insert (j, v) Z) := by
        have := Finset.card_nsmul_le_sum (block Z j)ᶜ (fun v => cnt (insert (j, v) Z)) _ hout
        rwa [nsmul_eq_mul] at this
      have h3 : ((block Z j)ᶜ.card : ℝ) = (m : ℝ) - (block Z j).card := by
        rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (by
          simpa using Finset.card_le_univ (block Z j))]
      rw [h3] at h2
      linarith
    have har := arith ((block Z j).card) m M (cnt Z) (by positivity)
      (hb j (Finset.mem_insert_self j R)) hx (hcntM Z)
    have hmr : (0:ℝ) < m := by exact_mod_cast hmpos
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hmr
    linarith

theorem main_count (X : HalfSet m) (hbal : Balanced X) (hne : g X ≠ 0) :
    (m : ℝ) ^ (2 * m) / 4 ≤ propagatedPairs g X := by
  classical
  set M : ℝ := (m : ℝ) ^ m with hM
  let P : Selector m → Selector m → Prop := fun γ γ' =>
    g (X ∪ selected γ) ≠ 0 ∨ g (X \ selected γ) ≠ 0 ∨
      g (xorSet X (selected γ) ∪ selected γ') ≠ 0
  let c : Selector m → ℝ := fun γ => ((Finset.univ.filter (fun γ' => P γ γ')).card : ℝ)
  have hpp : (propagatedPairs g X : ℝ) = ∑ γ, c γ := by
    have : propagatedPairs g X = ∑ γ : Selector m,
        (Finset.univ.filter (fun γ' => P γ γ')).card := by
      unfold propagatedPairs
      rw [Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro γ _
      rw [Finset.card_filter]
    simp only [c]
    exact_mod_cast this
  have hfull : ∀ γ, (g (X ∪ selected γ) ≠ 0 ∨ g (X \ selected γ) ≠ 0) → c γ = M := by
    intro γ h
    have : Finset.univ.filter (fun γ' => P γ γ') = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro γ' _
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    simp only [c]
    rw [this, Finset.card_univ, card_selector]
  have hc0 : ∀ γ, 0 ≤ c γ := fun γ => by positivity
  have hMM : (m : ℝ) ^ (2 * m) = M * M := by rw [hM, two_mul, pow_add]
  rw [hpp, hMM]
  have hbX : ∀ i ∈ (Finset.univ : Finset (Fin m)), (m : ℝ) / 4 ≤ (block X i).card := by
    intro i _; linarith [(hbal i).1]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- negative case: every γ contributes at least M/4
    have hγ : ∀ γ, M / 4 ≤ c γ := by
      intro γ
      by_cases h : g (X ∪ selected γ) ≠ 0 ∨ g (X \ selected γ) ≠ 0
      · rw [hfull γ h]
        have : (0:ℝ) ≤ M := by positivity
        linarith
      · push Not at h
        have hp := hpair X (xorSet X (selected γ)) (comparable_xor X γ)
        have hu : X ∪ xorSet X (selected γ) = X ∪ selected γ := by
          ext q; simp only [xorSet, Finset.mem_union, Finset.mem_sdiff]; tauto
        have hi : X ∩ xorSet X (selected γ) = X \ selected γ := by
          ext q; simp only [xorSet, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
          tauto
        rw [hu, hi, h.1, h.2] at hp
        have hpos' : 0 < g (xorSet X (selected γ)) := by linarith
        have hb' : ∀ i ∈ (Finset.univ : Finset (Fin m)),
            (m : ℝ) / 4 ≤ (block (xorSet X (selected γ)) i).card := by
          intro i _
          linarith [(hbal i).1, xor_block_card X γ i]
        have := positive g hpair Finset.univ _ hpos' hb'
        refine this.trans ?_
        simp only [c, img_univ]
        exact_mod_cast Finset.card_le_card (fun γ' hγ' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ' ⊢
          exact Or.inr (Or.inr hγ'))
    calc M * M / 4 = ∑ _γ : Selector m, M / 4 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_selector]; ring
      _ ≤ ∑ γ, c γ := Finset.sum_le_sum (fun γ _ => hγ γ)
  · -- positive case
    have hcount := positive g hpair Finset.univ X hpos hbX
    have hγ : ∀ γ, (if g (X ∪ selected γ) ≠ 0 then M else 0) ≤ c γ := by
      intro γ
      split_ifs with h
      · rw [hfull γ (Or.inl h)]
      · exact hc0 γ
    calc M * M / 4 = M * (M / 4) := by ring
      _ ≤ M * ((Finset.univ.filter (fun γ : Selector m =>
            g (X ∪ img Finset.univ γ) ≠ 0)).card : ℝ) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = ∑ γ : Selector m, (if g (X ∪ selected γ) ≠ 0 then M else 0) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            nsmul_eq_mul]
          rw [mul_comm]; rfl
      _ ≤ ∑ γ, c γ := Finset.sum_le_sum (fun γ _ => hγ γ)

end positive

end BTHelper_repair_propagation

theorem solution {m : ℕ} (hm : 1 ≤ m) (r : Sample m)
    (G : Oracle (Coord m)) (hG : Submodular G) (side : Bool) (fixed X : HalfSet m)
    (τ : Bool) (hbal : Balanced X) (hne : residual r G side fixed τ X ≠ 0) :
    (m : ℝ) ^ (2 * m) / 4 ≤ propagatedPairs (residual r G side fixed τ) X :=
  BTHelper_repair_propagation.main_count (residual r G side fixed τ)
    (BTHelper_repair_propagation.pair r G hG side fixed τ) X hbal hne
