-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.lovasz_convex_iff_submodular
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:58:13.160989+00:00
-- url     : https://prove2.me/submissions/0faba0b0-81c1-4ff9-bd22-60d481617315

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_LovaszExtension
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop
import Definitions.Def_DiscreteConvex_MConvexSetsB_IsConvexWithTop



namespace DiscreteConvex.MConvexSetsB

section LovCore

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma lv_sorted (p : V → ℝ) : (SortedValues p).SortedGT := by
  unfold SortedValues; exact Finset.sortedGT_sort _

lemma lv_strict (p : V → ℝ) {i j : ℕ} (hij : i < j) (hj : j < (SortedValues p).length) :
    (SortedValues p).getD j 0 < (SortedValues p).getD i 0 := by
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by omega)]
  exact (lv_sorted p).getElem_gt_getElem_of_lt hij

lemma lv_mem (p : V → ℝ) (v : V) : ∃ j < (SortedValues p).length,
    (SortedValues p).getD j 0 = p v := by
  have : p v ∈ SortedValues p := by
    unfold SortedValues; rw [Finset.mem_sort]; simp
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem this
  exact ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj, he]⟩

lemma tele (a : ℕ → ℝ) (j n : ℕ) (h : j ≤ n) :
    ∑ i ∈ Finset.range n, (if j ≤ i then a i - a (i+1) else 0) = a j - a n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]; · ring
    intro i hi; rw [Finset.mem_range] at hi; rw [if_neg (by omega)]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_pos hn]; ring

/-- Abel summation identity for an abstract strictly decreasing value list. -/
lemma abel_id (a : ℕ → ℝ) (m : ℕ) (p w : V → ℝ)
    (hstr : ∀ i j, i < j → j < m → a j < a i) (hmem : ∀ v, ∃ j < m, a j = p v) :
    ∑ v, p v * w v = ∑ i ∈ Finset.range (m-1), (a i - a (i+1)) *
        ∑ v ∈ Finset.univ.filter (fun v => a i ≤ p v), w v +
      a (m-1) * ∑ v ∈ Finset.univ.filter (fun v => a (m-1) ≤ p v), w v := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  obtain ⟨j, hj, hjv⟩ := hmem v
  have h1 : ∀ i ∈ Finset.range (m-1), ((a i - a (i+1)) * if a i ≤ p v then w v else 0) =
      (if j ≤ i then a i - a (i+1) else 0) * w v := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hji : j ≤ i
    · rw [if_pos hji, if_pos]
      rcases eq_or_lt_of_le hji with h | h
      · rw [← h, hjv]
      · exact le_of_lt (hjv ▸ hstr j i h (by omega))
    · rw [if_neg hji, if_neg]; · ring
      push_neg at hji ⊢
      rw [← hjv]; exact hstr i j hji hj
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, tele a j (m-1) (by omega)]
  have h2 : a (m-1) ≤ p v := by
    rcases eq_or_lt_of_le (show j ≤ m - 1 by omega) with h | h
    · rw [← h, hjv]
    · rw [← hjv]; exact le_of_lt (hstr j (m-1) h (by omega))
  rw [if_pos h2, ← hjv]; ring

noncomputable def tr (x : WithTop ℝ) : ℝ := WithTop.recTopCoe 0 (fun r => r) x
lemma tr_coe {x : WithTop ℝ} (h : x ≠ ⊤) : ((tr x : ℝ) : WithTop ℝ) = x := by
  induction x using WithTop.recTopCoe
  · exact absurd rfl h
  · rfl
lemma tr_real (r : ℝ) : tr (r : WithTop ℝ) = r := rfl

lemma S_coe (c r : ℝ) : ScalarWithTop c (r : WithTop ℝ) = ((c * r : ℝ) : WithTop ℝ) := rfl
lemma S_top {c : ℝ} (hc : c ≠ 0) : ScalarWithTop c ⊤ = ⊤ := by simp [ScalarWithTop, hc]
lemma S_zero (x : WithTop ℝ) : ScalarWithTop 0 x = 0 := by
  induction x using WithTop.recTopCoe <;> simp [ScalarWithTop]
lemma S_one (x : WithTop ℝ) : ScalarWithTop 1 x = x := by
  induction x using WithTop.recTopCoe <;> simp [ScalarWithTop]

lemma levelset_eq (p : V → ℝ) (i : ℕ) :
    LevelSet p (i+1) = Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v) := by
  ext v; simp [LevelSet]

lemma levelset_m (p : V → ℝ) : LevelSet p (SortedValues p).length = Finset.univ := by
  ext v; simp only [LevelSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  obtain ⟨j, hj, hjv⟩ := lv_mem p v
  rcases eq_or_lt_of_le (show j ≤ (SortedValues p).length - 1 by omega) with h | h
  · rw [← h, hjv]
  · rw [← hjv]; exact le_of_lt (lv_strict p h (by omega))

lemma filter_last (p : V → ℝ) :
    Finset.univ.filter (fun v => (SortedValues p).getD ((SortedValues p).length - 1) 0 ≤ p v)
      = Finset.univ := by
  rw [← levelset_m p]; ext v; simp [LevelSet]

lemma lov_eq (ρ : Finset V → WithTop ℝ) (p : V → ℝ) :
    LovaszExtension ρ p = (∑ i ∈ Finset.range ((SortedValues p).length - 1),
      ScalarWithTop ((SortedValues p).getD i 0 - (SortedValues p).getD (i+1) 0)
        (ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v)))) +
      ScalarWithTop ((SortedValues p).getD ((SortedValues p).length - 1) 0) (ρ Finset.univ) := by
  unfold LovaszExtension
  simp only [levelset_eq, levelset_m]

lemma lov_fin (ρ : Finset V → WithTop ℝ) (p : V → ℝ) (hV : ρ Finset.univ ≠ ⊤)
    (hfin : ∀ i < (SortedValues p).length - 1,
      ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v)) ≠ ⊤) :
    LovaszExtension ρ p = ((∑ i ∈ Finset.range ((SortedValues p).length - 1),
      ((SortedValues p).getD i 0 - (SortedValues p).getD (i+1) 0) *
        tr (ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v))) +
      (SortedValues p).getD ((SortedValues p).length - 1) 0 * tr (ρ Finset.univ) : ℝ)
        : WithTop ℝ) := by
  rw [lov_eq, WithTop.coe_add, WithTop.coe_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [← S_coe, tr_coe (hfin i hi)]
  · rw [← S_coe, tr_coe hV]

lemma lov_top (ρ : Finset V → WithTop ℝ) (p : V → ℝ)
    (h : ∃ i < (SortedValues p).length - 1,
      ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v)) = ⊤) :
    LovaszExtension ρ p = ⊤ := by
  obtain ⟨i, hi, hti⟩ := h
  rw [lov_eq]
  have : (∑ i ∈ Finset.range ((SortedValues p).length - 1),
      ScalarWithTop ((SortedValues p).getD i 0 - (SortedValues p).getD (i+1) 0)
        (ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v)))) = ⊤ := by
    rw [WithTop.sum_eq_top]
    refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    rw [hti]; apply S_top
    have := lv_strict p (show i < i + 1 by omega) (by omega)
    linarith
  rw [this, WithTop.top_add]

lemma lin_le (ρ : Finset V → WithTop ℝ) (p w : V → ℝ) (hV : ρ Finset.univ ≠ ⊤)
    (hw : ∀ X : Finset V, ((∑ v ∈ X, w v : ℝ) : WithTop ℝ) ≤ ρ X)
    (hwV : ((∑ v, w v : ℝ) : WithTop ℝ) = ρ Finset.univ) :
    ((∑ v, p v * w v : ℝ) : WithTop ℝ) ≤ LovaszExtension ρ p := by
  by_cases h : ∃ i < (SortedValues p).length - 1,
      ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v)) = ⊤
  · rw [lov_top ρ p h]; exact le_top
  push_neg at h
  rw [lov_fin ρ p hV h, WithTop.coe_le_coe,
    abel_id (fun i => (SortedValues p).getD i 0) _ p w (fun i j hij hj => lv_strict p hij hj)
      (lv_mem p), filter_last]
  have hV' : ∑ v, w v = tr (ρ Finset.univ) := by
    rw [← WithTop.coe_eq_coe, tr_coe hV]; exact hwV
  rw [hV']
  gcongr with i hi
  · rw [Finset.mem_range] at hi
    have := lv_strict p (show i < i + 1 by omega) (by omega)
    linarith
  · rw [Finset.mem_range] at hi
    have := hw (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v))
    rw [← tr_coe (h i hi), WithTop.coe_le_coe] at this
    exact this

lemma lin_eq (ρ : Finset V → WithTop ℝ) (p w : V → ℝ) (hV : ρ Finset.univ ≠ ⊤)
    (hw : ∀ i < (SortedValues p).length - 1,
      ((∑ v ∈ Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v), w v : ℝ)
        : WithTop ℝ) = ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v)))
    (hwV : ((∑ v, w v : ℝ) : WithTop ℝ) = ρ Finset.univ) :
    LovaszExtension ρ p = ((∑ v, p v * w v : ℝ) : WithTop ℝ) := by
  have h : ∀ i < (SortedValues p).length - 1,
      ρ (Finset.univ.filter (fun v => (SortedValues p).getD i 0 ≤ p v)) ≠ ⊤ := by
    intro i hi; rw [← hw i hi]; exact WithTop.coe_ne_top
  rw [lov_fin ρ p hV h, WithTop.coe_eq_coe,
    abel_id (fun i => (SortedValues p).getD i 0) _ p w (fun i j hij hj => lv_strict p hij hj)
      (lv_mem p), filter_last]
  have hV' : ∑ v, w v = tr (ρ Finset.univ) := by
    rw [← WithTop.coe_eq_coe, tr_coe hV]; exact hwV
  rw [hV']
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  congr 1
  have := hw i hi
  rw [← tr_coe (h i hi), WithTop.coe_eq_coe] at this
  exact this.symm

lemma bp_ne_top_of_add_ne_top {a b : WithTop ℝ} (h : a + b ≠ ⊤) : a ≠ ⊤ ∧ b ≠ ⊤ := by
  refine ⟨fun ha => h (by simp [ha]), fun hb => h (by simp [hb])⟩

/-- Submodularity at two finite values, read off in `ℝ`. -/
lemma bp_submod_real {a b c d : WithTop ℝ} (h : a + b ≥ c + d) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ∃ hc : c ≠ ⊤, ∃ hd : d ≠ ⊤, c.untop hc + d.untop hd ≤ a.untop ha + b.untop hb := by
  have hab : a + b ≠ ⊤ := by simp [ha, hb]
  have hcd : c + d ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt h (lt_top_iff_ne_top.mpr hab))
  obtain ⟨hc, hd⟩ := bp_ne_top_of_add_ne_top hcd
  refine ⟨hc, hd, ?_⟩
  have e1 : a = ((a.untop ha : ℝ) : WithTop ℝ) := (WithTop.coe_untop a ha).symm
  have e2 : b = ((b.untop hb : ℝ) : WithTop ℝ) := (WithTop.coe_untop b hb).symm
  have e3 : c = ((c.untop hc : ℝ) : WithTop ℝ) := (WithTop.coe_untop c hc).symm
  have e4 : d = ((d.untop hd : ℝ) : WithTop ℝ) := (WithTop.coe_untop d hd).symm
  rw [e1, e2, e3, e4, ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at h
  exact h

theorem bp_core {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ (n : ℕ) (W : Finset V), W.card = n → ∀ σ : Finset V → WithTop ℝ, σ ∅ = 0 → σ W ≠ ⊤ →
      (∀ X Y : Finset V, σ X + σ Y ≥ σ (X ∪ Y) + σ (X ∩ Y)) →
      ∃ x : V → ℝ, (∀ X ⊆ W, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ σ X) ∧
        ((∑ v ∈ W, x v : ℝ) : WithTop ℝ) = σ W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW σ hσ0 hσW hsub
  rcases W.eq_empty_or_nonempty with hWe | hWne
  · subst hWe
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro X hX
      rw [Finset.subset_empty.mp hX, hσ0]; simp
    · rw [hσ0]; simp
  -- a minimal nonempty finite-valued subset `S1` of `W`
  set F := W.powerset.filter (fun S => S.Nonempty ∧ σ S ≠ ⊤) with hF
  have hWF : W ∈ F := by simp [hF, hWne, hσW]
  obtain ⟨S1, hS1F, hS1min⟩ := Finset.exists_min_image F Finset.card ⟨W, hWF⟩
  simp only [hF, Finset.mem_filter, Finset.mem_powerset] at hS1F
  obtain ⟨hS1W, hS1ne, hS1top⟩ := hS1F
  have hmin : ∀ T ⊆ S1, T.Nonempty → σ T ≠ ⊤ → T = S1 := by
    intro T hT hTne hTtop
    have hTF : T ∈ F := by
      simp only [hF, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hT.trans hS1W, hTne, hTtop⟩
    exact Finset.eq_of_subset_of_card_le hT (hS1min T hTF)
  set r : ℝ := (σ S1).untop hS1top with hr
  have hσS1 : σ S1 = (r : WithTop ℝ) := (WithTop.coe_untop _ hS1top).symm
  -- the contracted function on `W \ S1`
  set σ' : Finset V → WithTop ℝ := fun Y => σ (S1 ∪ Y) + ((-r : ℝ) : WithTop ℝ) with hσ'
  have hσ'0 : σ' ∅ = 0 := by
    simp only [hσ', Finset.union_empty, hσS1, ← WithTop.coe_add]; simp
  set W' := W \ S1 with hW'
  have hS1W' : S1 ∪ W' = W := Finset.union_sdiff_of_subset hS1W
  have hσ'W : σ' W' ≠ ⊤ := by
    simp only [hσ', hS1W']; simp [hσW]
  have hsub' : ∀ X Y : Finset V, σ' X + σ' Y ≥ σ' (X ∪ Y) + σ' (X ∩ Y) := by
    intro X Y
    have h1 := hsub (S1 ∪ X) (S1 ∪ Y)
    have hu : (S1 ∪ X) ∪ (S1 ∪ Y) = S1 ∪ (X ∪ Y) := by
      ext a; simp only [Finset.mem_union]; tauto
    have hi : (S1 ∪ X) ∩ (S1 ∪ Y) = S1 ∪ (X ∩ Y) := (Finset.union_inter_distrib_left _ _ _).symm
    rw [hu, hi] at h1
    simp only [hσ', ge_iff_le]
    calc σ (S1 ∪ (X ∪ Y)) + ((-r : ℝ) : WithTop ℝ) + (σ (S1 ∪ (X ∩ Y)) + ((-r : ℝ) : WithTop ℝ))
        = (σ (S1 ∪ (X ∪ Y)) + σ (S1 ∪ (X ∩ Y))) + (((-r : ℝ) : WithTop ℝ) + ((-r : ℝ) : WithTop ℝ)) := by
          rw [add_add_add_comm]
      _ ≤ (σ (S1 ∪ X) + σ (S1 ∪ Y)) + (((-r : ℝ) : WithTop ℝ) + ((-r : ℝ) : WithTop ℝ)) := by
          gcongr
      _ = σ (S1 ∪ X) + ((-r : ℝ) : WithTop ℝ) + (σ (S1 ∪ Y) + ((-r : ℝ) : WithTop ℝ)) := by
          rw [add_add_add_comm]
  have hcard : W'.card < n := by
    rw [← hW, hW', Finset.card_sdiff_of_subset hS1W]
    have := hS1ne.card_pos
    have := Finset.card_le_card hS1W
    omega
  obtain ⟨x', hx'1, hx'2⟩ := ih W'.card hcard W' rfl σ' hσ'0 hσ'W hsub'
  obtain ⟨t, ht⟩ := hS1ne
  set x : V → ℝ := fun v => if v ∈ S1 then (if v = t then r else 0) else x' v with hx
  -- sums of `x`
  have hsumS1 : ∀ X : Finset V, X ∩ S1 = S1 → ∑ v ∈ X ∩ S1, x v = r := by
    intro X hX
    rw [hX, Finset.sum_congr rfl (g := fun v => if v = t then r else 0)
      (fun v hv => by simp only [hx, if_pos hv])]
    rw [Finset.sum_ite_eq' S1 t (fun _ => r)]; simp [ht]
  have hsumE : ∀ X : Finset V, X ∩ S1 = ∅ → ∑ v ∈ X ∩ S1, x v = 0 := by
    intro X hX; rw [hX]; simp
  have hsumD : ∀ X : Finset V, ∑ v ∈ X \ S1, x v = ∑ v ∈ X \ S1, x' v := by
    intro X
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have : v ∉ S1 := (Finset.mem_sdiff.mp hv).2
    simp [hx, this]
  have hsplit : ∀ X : Finset V, ∑ v ∈ X, x v = ∑ v ∈ X ∩ S1, x v + ∑ v ∈ X \ S1, x' v := by
    intro X; rw [← hsumD, Finset.sum_inter_add_sum_sdiff]
  refine ⟨x, ?_, ?_⟩
  · intro X hXW
    by_cases hXtop : σ X = ⊤
    · rw [hXtop]; exact le_top
    have hsX := hsub X S1
    obtain ⟨hU, hI, hreal⟩ := bp_submod_real hsX hXtop hS1top
    have hXS1W' : X \ S1 ⊆ W' := Finset.sdiff_subset_sdiff hXW le_rfl
    have hx'X := hx'1 (X \ S1) hXS1W'
    rcases (X ∩ S1).eq_empty_or_nonempty with hE | hNE
    · -- `X` misses `S1`
      have hXd : X \ S1 = X := by
        ext a; simp only [Finset.mem_sdiff]
        constructor
        · exact fun h => h.1
        · intro ha; refine ⟨ha, fun hb => ?_⟩
          have : a ∈ X ∩ S1 := Finset.mem_inter.mpr ⟨ha, hb⟩
          rw [hE] at this; simp at this
      rw [hsplit, hsumE X hE, zero_add]
      rw [hXd] at hx'X ⊢
      simp only [hσ'] at hx'X
      have hU' : σ (S1 ∪ X) ≠ ⊤ := by rwa [Finset.union_comm]
      rw [← WithTop.coe_untop _ hU', ← WithTop.coe_add, WithTop.coe_le_coe] at hx'X
      rw [← WithTop.coe_untop _ hXtop, WithTop.coe_le_coe]
      have hI0 : (σ (X ∩ S1)).untop hI = 0 := by
        have : σ (X ∩ S1) = 0 := by rw [hE, hσ0]
        simp [this]
      have hUeq : (σ (X ∪ S1)).untop hU = (σ (S1 ∪ X)).untop hU' := by
        simp [Finset.union_comm]
      have : (σ S1).untop hS1top = r := rfl
      linarith
    · -- `X` contains `S1`
      have hXS : X ∩ S1 = S1 := hmin _ Finset.inter_subset_right hNE hI
      have hS1X : S1 ⊆ X := by rw [← hXS]; exact Finset.inter_subset_left
      rw [hsplit, hsumS1 X hXS]
      have hUX : S1 ∪ (X \ S1) = X := Finset.union_sdiff_of_subset hS1X
      simp only [hσ', hUX] at hx'X
      rw [← WithTop.coe_untop _ hXtop, ← WithTop.coe_add, WithTop.coe_le_coe] at hx'X
      rw [← WithTop.coe_untop _ hXtop, WithTop.coe_le_coe]
      linarith
  · rw [hsplit, hsumS1 W (Finset.inter_eq_right.mpr hS1W)]
    have hW'eq : W \ S1 = W' := rfl
    rw [hW'eq, WithTop.coe_add, hx'2]
    simp only [hσ', hS1W']
    rw [← WithTop.coe_untop _ hσW, ← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    ring

lemma chain_mono (C : ℕ → Finset V) (k : ℕ) (hmono : ∀ i < k, C i ⊆ C (i+1)) :
    ∀ i j, i ≤ j → j ≤ k → C i ⊆ C j := by
  intro i j hij hjk
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (hmono n (by omega))

theorem greedy_chain (ρ : Finset V → WithTop ℝ) (h0 : ρ ∅ = 0)
    (hsub : ∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y))
    (C : ℕ → Finset V) (k : ℕ) (hC0 : C 0 = ∅) (hmono : ∀ i < k, C i ⊆ C (i+1))
    (hfin : ∀ i ≤ k, ρ (C i) ≠ ⊤) :
    ∀ j ≤ k, ∃ w : V → ℝ, (∀ X ⊆ C j, ((∑ v ∈ X, w v : ℝ) : WithTop ℝ) ≤ ρ X) ∧
      ∀ i ≤ j, ((∑ v ∈ C i, w v : ℝ) : WithTop ℝ) = ρ (C i) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro X hX; rw [hC0, Finset.subset_empty] at hX; subst hX; rw [h0]; simp
    · intro i hi; have : i = 0 := by omega
      subst this; rw [hC0, h0]; simp
  | succ j ih =>
    intro hjk
    obtain ⟨w, hw1, hw2⟩ := ih (by omega)
    set B := C j with hB
    have hBt := hfin j (by omega)
    set rB : ℝ := tr (ρ B) with hrB
    have hρB : ρ B = (rB : WithTop ℝ) := (tr_coe hBt).symm
    have hBC : B ⊆ C (j+1) := hmono j (by omega)
    set L := C (j+1) \ B with hL
    set σ : Finset V → WithTop ℝ := fun X => ρ (B ∪ (X ∩ L)) + ((-rB : ℝ) : WithTop ℝ) with hσ
    have hσ0 : σ ∅ = 0 := by
      simp only [hσ, Finset.empty_inter, Finset.union_empty, hρB, ← WithTop.coe_add]; simp
    have hBL : B ∪ (L ∩ L) = C (j+1) := by
      rw [Finset.inter_self, hL, Finset.union_sdiff_of_subset hBC]
    have hσL : σ L ≠ ⊤ := by
      simp only [hσ, hBL]; simp [hfin (j+1) hjk]
    have hsubσ : ∀ X Y : Finset V, σ X + σ Y ≥ σ (X ∪ Y) + σ (X ∩ Y) := by
      intro X Y
      have h1 := hsub (B ∪ (X ∩ L)) (B ∪ (Y ∩ L))
      have hu : (B ∪ (X ∩ L)) ∪ (B ∪ (Y ∩ L)) = B ∪ ((X ∪ Y) ∩ L) := by
        ext a; simp only [Finset.mem_union, Finset.mem_inter]; tauto
      have hi : (B ∪ (X ∩ L)) ∩ (B ∪ (Y ∩ L)) = B ∪ ((X ∩ Y) ∩ L) := by
        ext a; simp only [Finset.mem_union, Finset.mem_inter]; tauto
      rw [hu, hi] at h1
      simp only [hσ, ge_iff_le]
      calc ρ (B ∪ ((X ∪ Y) ∩ L)) + ((-rB : ℝ) : WithTop ℝ) + (ρ (B ∪ ((X ∩ Y) ∩ L)) + ((-rB : ℝ) : WithTop ℝ))
          = (ρ (B ∪ ((X ∪ Y) ∩ L)) + ρ (B ∪ ((X ∩ Y) ∩ L))) + (((-rB : ℝ) : WithTop ℝ) + ((-rB : ℝ) : WithTop ℝ)) := by
            rw [add_add_add_comm]
        _ ≤ (ρ (B ∪ (X ∩ L)) + ρ (B ∪ (Y ∩ L))) + (((-rB : ℝ) : WithTop ℝ) + ((-rB : ℝ) : WithTop ℝ)) := by
            gcongr
        _ = ρ (B ∪ (X ∩ L)) + ((-rB : ℝ) : WithTop ℝ) + (ρ (B ∪ (Y ∩ L)) + ((-rB : ℝ) : WithTop ℝ)) := by
            rw [add_add_add_comm]
    obtain ⟨x, hx1, hx2⟩ := bp_core _ L rfl σ hσ0 hσL hsubσ
    set w' : V → ℝ := fun v => if v ∈ B then w v else x v with hw'
    have hsplit : ∀ X : Finset V, ∑ v ∈ X, w' v = ∑ v ∈ X ∩ B, w v + ∑ v ∈ X \ B, x v := by
      intro X
      rw [← Finset.sum_inter_add_sum_sdiff X B]
      congr 1
      · exact Finset.sum_congr rfl (fun v hv => by simp [hw', (Finset.mem_inter.mp hv).2])
      · exact Finset.sum_congr rfl (fun v hv => by simp [hw', (Finset.mem_sdiff.mp hv).2])
    refine ⟨w', ?_, ?_⟩
    · intro X hX
      by_cases hXt : ρ X = ⊤
      · rw [hXt]; exact le_top
      obtain ⟨hU, hI, hreal⟩ := bp_submod_real (hsub X B) hXt hBt
      have hXB : (X \ B) ∩ L = X \ B := by
        rw [Finset.inter_eq_left]; intro a ha
        rw [Finset.mem_sdiff] at ha ⊢; exact ⟨hX ha.1, ha.2⟩
      have hx := hx1 (X \ B) (by rw [← hXB]; exact Finset.inter_subset_right)
      simp only [hσ, hXB, Finset.union_sdiff_self_eq_union] at hx
      have hBX : B ∪ X = X ∪ B := Finset.union_comm _ _
      rw [hBX, ← tr_coe hU, ← WithTop.coe_add, WithTop.coe_le_coe] at hx
      have hw := hw1 (X ∩ B) Finset.inter_subset_right
      rw [← tr_coe hI, WithTop.coe_le_coe] at hw
      rw [hsplit, ← tr_coe hXt, WithTop.coe_le_coe]
      have e1 : (ρ (X ∪ B)).untop hU = tr (ρ (X ∪ B)) := by
        rw [← WithTop.coe_eq_coe, tr_coe hU]; simp
      have e2 : (ρ (X ∩ B)).untop hI = tr (ρ (X ∩ B)) := by
        rw [← WithTop.coe_eq_coe, tr_coe hI]; simp
      have e3 : (ρ X).untop hXt = tr (ρ X) := by
        rw [← WithTop.coe_eq_coe, tr_coe hXt]; simp
      have e4 : (ρ B).untop hBt = rB := by
        apply WithTop.coe_injective; rw [WithTop.coe_untop]; exact hρB
      rw [e1, e2, e3, e4] at hreal
      linarith
    · intro i hi
      rcases eq_or_lt_of_le hi with h | h
      · rw [h, hsplit, Finset.inter_eq_right.mpr hBC, ← hL]
        have := hw2 j le_rfl
        rw [← hB] at this
        rw [WithTop.coe_add, this, hx2]
        simp only [hσ, hBL, hρB]
        rw [← tr_coe (hfin (j+1) hjk), ← WithTop.coe_add, ← WithTop.coe_add]
        congr 1; ring
      · have hCi : C i ⊆ B := chain_mono C k hmono i j (by omega) (by omega)
        rw [hsplit, Finset.inter_eq_left.mpr hCi, Finset.sdiff_eq_empty_iff_subset.mpr hCi,
          Finset.sum_empty, add_zero]
        exact hw2 i (by omega)

lemma union_fin (ρ : Finset V → WithTop ℝ)
    (hsub : ∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)) {X Y : Finset V}
    (hX : ρ X ≠ ⊤) (hY : ρ Y ≠ ⊤) : ρ (X ∪ Y) ≠ ⊤ ∧ ρ (X ∩ Y) ≠ ⊤ := by
  obtain ⟨h1, h2, _⟩ := bp_submod_real (hsub X Y) hX hY
  exact ⟨h1, h2⟩

lemma biUnion_fin (ρ : Finset V → WithTop ℝ) (h0 : ρ ∅ = 0)
    (hsub : ∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y))
    (g : V → Finset V) (hg : ∀ v, ρ (g v) ≠ ⊤) (s : Finset V) : ρ (s.biUnion g) ≠ ⊤ := by
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s _ ih =>
    rw [Finset.biUnion_insert]
    exact (union_fin ρ hsub (hg a) ih).1

lemma lvl_fin (ρ : Finset V → WithTop ℝ) (hV : ρ Finset.univ ≠ ⊤) (p : V → ℝ)
    (hp : LovaszExtension ρ p ≠ ⊤) (v0 : V) :
    ρ (Finset.univ.filter (fun v => p v0 ≤ p v)) ≠ ⊤ := by
  obtain ⟨j, hj, hjv⟩ := lv_mem p v0
  rw [← hjv]
  by_cases hjm : j < (SortedValues p).length - 1
  · intro htop; exact hp (lov_top ρ p ⟨j, hjm, htop⟩)
  · have : j = (SortedValues p).length - 1 := by omega
    rw [this, filter_last]; exact hV

lemma z_level (x y : V → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : ℝ) :
    Finset.univ.filter (fun v => c ≤ t * x v + (1 - t) * y v) =
      (Finset.univ.filter (fun v => c ≤ t * x v + (1 - t) * y v)).biUnion
        (fun v0 => Finset.univ.filter (fun v => x v0 ≤ x v) ∩
          Finset.univ.filter (fun v => y v0 ≤ y v)) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · intro h; exact ⟨v, h, le_rfl, le_rfl⟩
  · rintro ⟨v0, h0, hx, hy⟩
    have h1 : t * x v0 ≤ t * x v := mul_le_mul_of_nonneg_left hx ht0
    have h2 : (1 - t) * y v0 ≤ (1 - t) * y v := mul_le_mul_of_nonneg_left hy (by linarith)
    linarith

theorem sub_to_convex (ρ : Finset V → WithTop ℝ) (h0 : ρ ∅ = 0) (hV : ρ Finset.univ ≠ ⊤)
    (hsub : ∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)) :
    IsConvexWithTop (LovaszExtension ρ) := by
  intro x y t ht0 ht1
  rcases eq_or_lt_of_le ht0 with h | htp
  · subst h
    have : (fun v => 0 * x v + (1 - 0) * y v) = y := by funext v; ring
    rw [this, S_zero, show (1:ℝ) - 0 = 1 by norm_num, S_one, zero_add]
  rcases eq_or_lt_of_le ht1 with h | htq
  · subst h
    have : (fun v => 1 * x v + (1 - 1) * y v) = x := by funext v; ring
    rw [this, S_one, show (1:ℝ) - 1 = 0 by norm_num, S_zero, add_zero]
  by_cases hx : LovaszExtension ρ x = ⊤
  · rw [hx, S_top (by linarith), WithTop.top_add]; exact le_top
  by_cases hy : LovaszExtension ρ y = ⊤
  · rw [hy, S_top (by linarith), WithTop.add_top]; exact le_top
  set z : V → ℝ := fun v => t * x v + (1 - t) * y v with hz
  have hzc : ∀ c, ρ (Finset.univ.filter (fun v => c ≤ z v)) ≠ ⊤ := by
    intro c
    rw [hz, z_level x y t ht0 ht1 c]
    apply biUnion_fin ρ h0 hsub
    intro v0
    exact (union_fin ρ hsub (lvl_fin ρ hV x hx v0) (lvl_fin ρ hV y hy v0)).2
  set a := fun i => (SortedValues z).getD i 0 with ha
  set k := (SortedValues z).length with hk
  set C : ℕ → Finset V := fun i =>
    if i = 0 then ∅ else Finset.univ.filter (fun v => a (i-1) ≤ z v) with hC
  have hC0 : C 0 = ∅ := by simp [hC]
  have hmono : ∀ i < k, C i ⊆ C (i+1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, hC0]; exact Finset.empty_subset _
    · simp only [hC, if_neg (show i ≠ 0 by omega), if_neg (show i + 1 ≠ 0 by omega),
        show i + 1 - 1 = i by omega]
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have := lv_strict z (show i - 1 < i by omega) hi
      simp only [ha] at hv ⊢
      linarith
  have hfin : ∀ i ≤ k, ρ (C i) ≠ ⊤ := by
    intro i _
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, hC0, h0]; simp
    · simp only [hC, if_neg (show i ≠ 0 by omega)]; exact hzc _
  have hCk : C k = Finset.univ := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, hC0]; symm; rw [Finset.univ_eq_empty_iff]
      constructor; intro v
      obtain ⟨j, hj, _⟩ := lv_mem z v
      omega
    · simp only [hC, if_neg (show k ≠ 0 by omega)]; exact filter_last _
  obtain ⟨w, hw1, hw2⟩ := greedy_chain ρ h0 hsub C k hC0 hmono hfin k le_rfl
  rw [hCk] at hw1
  have hwX : ∀ X : Finset V, ((∑ v ∈ X, w v : ℝ) : WithTop ℝ) ≤ ρ X :=
    fun X => hw1 X (Finset.subset_univ X)
  have hwV : ((∑ v, w v : ℝ) : WithTop ℝ) = ρ Finset.univ := by
    have := hw2 k le_rfl; rw [hCk] at this; exact this
  have hzeq : LovaszExtension ρ z = ((∑ v, z v * w v : ℝ) : WithTop ℝ) := by
    apply lin_eq ρ z w hV _ hwV
    intro i hi
    have := hw2 (i+1) (by omega)
    simp only [hC, if_neg (show i + 1 ≠ 0 by omega), show i + 1 - 1 = i by omega, ha] at this
    exact this
  have hxle := lin_le ρ x w hV hwX hwV
  have hyle := lin_le ρ y w hV hwX hwV
  rw [← tr_coe hx] at hxle ⊢
  rw [← tr_coe hy] at hyle ⊢
  rw [WithTop.coe_le_coe] at hxle hyle
  rw [hzeq, S_coe, S_coe, ← WithTop.coe_add, WithTop.coe_le_coe]
  have hsum : ∑ v, z v * w v = t * ∑ v, x v * w v + (1 - t) * ∑ v, y v * w v := by
    simp only [hz, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [hsum]
  have h1 := mul_le_mul_of_nonneg_left hxle ht0
  have h2 := mul_le_mul_of_nonneg_left hyle (show (0:ℝ) ≤ 1 - t by linarith)
  linarith

lemma sv_eq (p : V → ℝ) (l : List ℝ) (hl : l.SortedGT) (hmem : ∀ r, r ∈ l ↔ ∃ v, p v = r) :
    SortedValues p = l := by
  apply (lv_sorted p).eq_of_mem_iff hl
  intro r
  unfold SortedValues; rw [Finset.mem_sort, hmem]; simp

lemma half_le {a b c d : WithTop ℝ}
    (h : ScalarWithTop (1/2) a + ScalarWithTop (1/2) b ≤ ScalarWithTop (1/2) c + ScalarWithTop (1/2) d) :
    a + b ≤ c + d := by
  have hh : (1/2 : ℝ) ≠ 0 := by norm_num
  induction c using WithTop.recTopCoe
  · simp
  induction d using WithTop.recTopCoe
  · simp
  induction a using WithTop.recTopCoe
  · rw [S_top hh, WithTop.top_add, S_coe, S_coe, ← WithTop.coe_add] at h
    exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
  induction b using WithTop.recTopCoe
  · rw [S_top hh, WithTop.add_top, S_coe, S_coe, ← WithTop.coe_add] at h
    exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
  rw [S_coe, S_coe, S_coe, S_coe, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

noncomputable def chi (X : Finset V) : V → ℝ := fun v => if v ∈ X then 1 else 0

lemma lov_chi (ρ : Finset V → WithTop ℝ) (X : Finset V) (hX : X.Nonempty)
    (hXV : X ≠ Finset.univ) : LovaszExtension ρ (chi X) = ρ X := by
  obtain ⟨u, hu⟩ := hX
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ X := by
    by_contra hc; push_neg at hc; exact hXV (Finset.eq_univ_iff_forall.mpr hc)
  have hs : SortedValues (chi X) = [1, 0] := by
    apply sv_eq
    · rw [List.sortedGT_iff_pairwise]; simp
    · intro r
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨u, by simp [chi, hu]⟩
        · exact ⟨u', by simp [chi, hu']⟩
      · rintro ⟨v, rfl⟩
        by_cases hv : v ∈ X <;> simp [chi, hv]
  rw [lov_eq, hs]
  have hf : Finset.univ.filter (fun v => (1:ℝ) ≤ chi X v) = X := by
    ext v; rw [Finset.mem_filter]; by_cases hv : v ∈ X <;> simp [chi, hv]
  simp [hf, S_one, S_zero]

lemma lov_mid (ρ : Finset V → WithTop ℝ) (h0 : ρ ∅ = 0) (X Y : Finset V) (hXY : ¬ X ⊆ Y)
    (hYX : ¬ Y ⊆ X) :
    LovaszExtension ρ (fun v => 1/2 * chi X v + (1 - 1/2) * chi Y v) =
      ScalarWithTop (1/2) (ρ (X ∩ Y)) + ScalarWithTop (1/2) (ρ (X ∪ Y)) := by
  set z : V → ℝ := fun v => 1/2 * chi X v + (1 - 1/2) * chi Y v with hz
  have hz1 : ∀ v, z v = 1 ↔ v ∈ X ∧ v ∈ Y := by
    intro v; by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hz, chi, hx, hy] <;> norm_num
  have hzh : ∀ v, z v = 1/2 ↔ (v ∈ X ∧ v ∉ Y) ∨ (v ∉ X ∧ v ∈ Y) := by
    intro v; by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hz, chi, hx, hy] <;> norm_num
  have hz0 : ∀ v, z v = 0 ↔ v ∉ X ∧ v ∉ Y := by
    intro v; by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hz, chi, hx, hy] <;> norm_num
  have hz3 : ∀ v, z v = 1 ∨ z v = 1/2 ∨ z v = 0 := by
    intro v; by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hz, chi, hx, hy] <;> norm_num
  have hF1 : Finset.univ.filter (fun v => (1:ℝ) ≤ z v) = X ∩ Y := by
    ext v; by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hz, chi, hx, hy] <;> norm_num
  have hFh : Finset.univ.filter (fun v => (1/2:ℝ) ≤ z v) = X ∪ Y := by
    ext v; by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp [hz, chi, hx, hy] <;> norm_num
  have hFh' : Finset.univ.filter (fun v => (2⁻¹:ℝ) ≤ z v) = X ∪ Y := by
    rw [← hFh]; norm_num
  have e' : (1:ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  obtain ⟨a, haX, haY⟩ := Finset.not_subset.mp hXY
  have hha : z a = 1/2 := (hzh a).mpr (Or.inl ⟨haX, haY⟩)
  have hh : (1/2 : ℝ) ≠ 0 := by norm_num
  rcases (X ∩ Y).eq_empty_or_nonempty with hI | ⟨b, hb⟩
  · -- no value 1
    have hn1 : ∀ v, z v ≠ 1 := by
      intro v hv; rw [hz1] at hv
      have : v ∈ X ∩ Y := Finset.mem_inter.mpr hv
      rw [hI] at this; simp at this
    rw [hI, h0]
    have hS0 : ScalarWithTop (1/2) (0 : WithTop ℝ) = 0 := by
      rw [show (0 : WithTop ℝ) = ((0:ℝ) : WithTop ℝ) by simp, S_coe]; simp
    rw [hS0, zero_add]
    by_cases hU : X ∪ Y = Finset.univ
    · have hs : SortedValues z = [1/2] := by
        apply sv_eq
        · rw [List.sortedGT_iff_pairwise]; simp
        · intro r
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro rfl; exact ⟨a, hha⟩
          · rintro ⟨v, rfl⟩
            rcases hz3 v with h | h | h
            · exact absurd h (hn1 v)
            · exact h
            · exfalso; rw [hz0] at h
              have : v ∈ X ∪ Y := by rw [hU]; exact Finset.mem_univ v
              rw [Finset.mem_union] at this; tauto
      rw [lov_eq, hs, hU]
      simp [hFh', e']
    · obtain ⟨c, hc⟩ : ∃ c, c ∉ X ∪ Y := by
        by_contra hc; push_neg at hc; exact hU (Finset.eq_univ_iff_forall.mpr hc)
      have hc0 : z c = 0 := (hz0 c).mpr (by rw [Finset.mem_union] at hc; tauto)
      have hs : SortedValues z = [1/2, 0] := by
        apply sv_eq
        · rw [List.sortedGT_iff_pairwise]; simp
        · intro r
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (rfl | rfl)
            · exact ⟨a, hha⟩
            · exact ⟨c, hc0⟩
          · rintro ⟨v, rfl⟩
            rcases hz3 v with h | h | h
            · exact absurd h (hn1 v)
            · exact Or.inl h
            · exact Or.inr h
      rw [lov_eq, hs]
      simp [hFh', S_zero]
  · have hb1 : z b = 1 := (hz1 b).mpr (Finset.mem_inter.mp hb)
    by_cases hU : X ∪ Y = Finset.univ
    · have hs : SortedValues z = [1, 1/2] := by
        apply sv_eq
        · rw [List.sortedGT_iff_pairwise]; simp; norm_num
        · intro r
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (rfl | rfl)
            · exact ⟨b, hb1⟩
            · exact ⟨a, hha⟩
          · rintro ⟨v, rfl⟩
            rcases hz3 v with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exfalso; rw [hz0] at h
              have : v ∈ X ∪ Y := by rw [hU]; exact Finset.mem_univ v
              rw [Finset.mem_union] at this; tauto
      rw [lov_eq, hs]
      have e : (1:ℝ) - 1/2 = 1/2 := by norm_num
      rw [hU]
      simp [hF1, e, e']
    · obtain ⟨c, hc⟩ : ∃ c, c ∉ X ∪ Y := by
        by_contra hc; push_neg at hc; exact hU (Finset.eq_univ_iff_forall.mpr hc)
      have hc0 : z c = 0 := (hz0 c).mpr (by rw [Finset.mem_union] at hc; tauto)
      have hs : SortedValues z = [1, 1/2, 0] := by
        apply sv_eq
        · rw [List.sortedGT_iff_pairwise]; simp; norm_num
        · intro r
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (rfl | rfl | rfl)
            · exact ⟨b, hb1⟩
            · exact ⟨a, hha⟩
            · exact ⟨c, hc0⟩
          · rintro ⟨v, rfl⟩
            exact hz3 v
      rw [lov_eq, hs]
      have e : (1:ℝ) - 1/2 = 1/2 := by norm_num
      simp [Finset.sum_range_succ, hF1, hFh', e, e', S_zero]

theorem convex_to_sub (ρ : Finset V → WithTop ℝ) (h0 : ρ ∅ = 0)
    (hc : IsConvexWithTop (LovaszExtension ρ)) (X Y : Finset V) :
    ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y) := by
  by_cases hXY : X ⊆ Y
  · rw [Finset.union_eq_right.mpr hXY, Finset.inter_eq_left.mpr hXY, add_comm]
  by_cases hYX : Y ⊆ X
  · rw [Finset.union_eq_left.mpr hYX, Finset.inter_eq_right.mpr hYX]
  have h := hc (chi X) (chi Y) (1/2) (by norm_num) (by norm_num)
  rw [lov_mid ρ h0 X Y hXY hYX] at h
  have hXne : X.Nonempty := by
    obtain ⟨a, ha, _⟩ := Finset.not_subset.mp hXY; exact ⟨a, ha⟩
  have hYne : Y.Nonempty := by
    obtain ⟨a, ha, _⟩ := Finset.not_subset.mp hYX; exact ⟨a, ha⟩
  have hXV : X ≠ Finset.univ := by
    intro h; exact hYX (h ▸ Finset.subset_univ Y)
  have hYV : Y ≠ Finset.univ := by
    intro h; exact hXY (h ▸ Finset.subset_univ X)
  rw [lov_chi ρ X hXne hXV, lov_chi ρ Y hYne hYV, show (1:ℝ) - 1/2 = 1/2 by norm_num] at h
  have := half_le h
  rw [ge_iff_le, add_comm (ρ (X ∪ Y))]; exact this

theorem lovasz_core (ρ : Finset V → WithTop ℝ) (hρ0 : ρ ∅ = 0) (hρV : ρ Finset.univ ≠ ⊤) :
    (∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)) ↔
      IsConvexWithTop (LovaszExtension ρ) :=
  ⟨fun h => sub_to_convex ρ hρ0 hρV h, fun h => convex_to_sub ρ hρ0 h⟩

end LovCore

end DiscreteConvex.MConvexSetsB

open DiscreteConvex.MConvexSetsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ0 : ρ ∅ = 0) (hρV : ρ Finset.univ ≠ ⊤) :
    (∀ X Y : Finset V, ρ X + ρ Y ≥ ρ (X ∪ Y) + ρ (X ∩ Y)) ↔ IsConvexWithTop (LovaszExtension ρ) := by
  exact lovasz_core ρ hρ0 hρV
