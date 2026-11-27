-- Prove2me | solution 1 for CirclePackingConstants.twentyfive_missing_cell_halfbox_bound
-- status  : ACCEPTED   (prove)
-- author  : @kylelyk
-- created : 2026-11-27T06:07:59.208117+00:00
-- url     : https://prove2.me/submissions/a5883f08-99ee-4d21-9e6b-0c0f912d1d33

import Definitions.Def_CirclePackingConstants_TwentyfiveNogoods
import Theorems.Thm_CirclePackingConstants_twentyfive_nogood_batch1
import Theorems.Thm_CirclePackingConstants_twentyfive_nogood_batch2
import Theorems.Thm_CirclePackingConstants_twentyfive_nogood_batch3
import Theorems.Thm_CirclePackingConstants_twentyfive_nogood_batch4
import Theorems.Thm_CirclePackingConstants_twentyfive_nogood_batch5
import Theorems.Thm_CirclePackingConstants_twentyfive_nogood_batch6
import Theorems.Thm_CirclePackingConstants_twentyfive_nogood_cover

/-!
Reduction of `twentyfive_missing_cell_halfbox_bound` to the nogood library:
* `twentyfive_nogood_batch1..6`: every pattern of `Twentyfive.nogoods` is infeasible;
* `twentyfive_nogood_cover`: every count vector (entries ≤ 2, sum 25, some entry 0) contains a placed pattern.
Infeasibility is invariant under the symmetries of the square and translations by whole cells and monotone
(`infeasible_transport`), and 25 half-cell points with an empty cell give a count vector (`halfbox_of_cover`).
-/

open CirclePackingConstants CirclePackingConstants.Twentyfive

namespace HalfboxReduction

/-- Inverse of the isometry of the unit square behind `trI k di dj`: undo the shift by `(di/5, dj/5)`, undo the
coordinate swap (bit 2 of `k`), undo the flips `x ↦ 1 - x` (bit 0) and `y ↦ 1 - y` (bit 1). -/
noncomputable def unT (k : ℕ) (di dj : ℤ) (P : Point) : Point :=
  (if k % 2 = 1 then 1 - (if (k / 4) % 2 = 1 then P.2 - (dj : ℝ) / 5 else P.1 - (di : ℝ) / 5)
    else (if (k / 4) % 2 = 1 then P.2 - (dj : ℝ) / 5 else P.1 - (di : ℝ) / 5),
   if (k / 2) % 2 = 1 then 1 - (if (k / 4) % 2 = 1 then P.1 - (di : ℝ) / 5 else P.2 - (dj : ℝ) / 5)
    else (if (k / 4) % 2 = 1 then P.1 - (di : ℝ) / 5 else P.2 - (dj : ℝ) / 5))

theorem sqDist_unT (k : ℕ) (di dj : ℤ) (P Q : Point) :
    sqDist (unT k di dj P) (unT k di dj Q) = sqDist P Q := by
  unfold unT sqDist
  split_ifs <;> dsimp only <;> ring

theorem cellIdx_div (i j : ℤ) (hi0 : 0 ≤ i) (hj0 : 0 ≤ j) (hj : j < 5) :
    (((5 * i + j).toNat / 5 : ℕ) : ℝ) = (i : ℝ) := by
  have h1 : ((5 * i + j).toNat / 5 : ℕ) = i.toNat := by omega
  rw [h1]
  exact_mod_cast Int.toNat_of_nonneg hi0

theorem cellIdx_mod (i j : ℤ) (hi0 : 0 ≤ i) (hj0 : 0 ≤ j) (hj : j < 5) :
    (((5 * i + j).toNat % 5 : ℕ) : ℝ) = (j : ℝ) := by
  have h1 : ((5 * i + j).toNat % 5 : ℕ) = j.toNat := by omega
  rw [h1]
  exact_mod_cast Int.toNat_of_nonneg hj0

theorem inCellR_unT (k : ℕ) (di dj : ℤ) (c : ℕ) (i j : ℤ) (P : Point)
    (ht : trI k di dj c = (i, j)) (hi0 : 0 ≤ i) (hj0 : 0 ≤ j) (hj : j < 5)
    (hP : InCellR P (5 * i + j).toNat) : InCellR (unT k di dj P) c := by
  unfold InCellR at hP ⊢
  rw [cellIdx_div i j hi0 hj0 hj, cellIdx_mod i j hi0 hj0 hj] at hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  unfold trI at ht
  unfold unT
  generalize c / 5 = u at ht ⊢
  generalize c % 5 = v at ht ⊢
  split_ifs at ht ⊢ <;> simp only [Prod.mk.injEq] at ht <;> obtain ⟨hi, hj'⟩ := ht <;>
    have hi' : (i : ℝ) = _ := congrArg (Int.cast (R := ℝ)) hi.symm <;>
    have hj'' : (j : ℝ) = _ := congrArg (Int.cast (R := ℝ)) hj'.symm <;>
    push_cast at hi' hj'' <;> dsimp only <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem trI_inj (k : ℕ) (di dj : ℤ) (c c' : ℕ) (h : trI k di dj c = trI k di dj c') : c = c' := by
  unfold trI at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega

theorem infeasible_transport (k : ℕ) (di dj : ℤ) (a b A B : ℕ) (hk : k < 8) (h : Infeasible a b)
    (hA : ∀ c, c < 25 → a.testBit c = true →
      0 ≤ (trI k di dj c).1 ∧ (trI k di dj c).1 < 5 ∧ 0 ≤ (trI k di dj c).2 ∧ (trI k di dj c).2 < 5 ∧
      A.testBit (5 * (trI k di dj c).1 + (trI k di dj c).2).toNat = true)
    (hB : ∀ c, c < 25 → b.testBit c = true →
      0 ≤ (trI k di dj c).1 ∧ (trI k di dj c).1 < 5 ∧ 0 ≤ (trI k di dj c).2 ∧ (trI k di dj c).2 < 5 ∧
      B.testBit (5 * (trI k di dj c).1 + (trI k di dj c).2).toNat = true) :
    Infeasible A B := by
  have _ := hk
  have hAB : ∀ l c, c < 25 → (layMask a b l).testBit c = true →
      0 ≤ (trI k di dj c).1 ∧ (trI k di dj c).1 < 5 ∧ 0 ≤ (trI k di dj c).2 ∧ (trI k di dj c).2 < 5 ∧
      (layMask A B l).testBit (5 * (trI k di dj c).1 + (trI k di dj c).2).toNat = true := by
    intro l c hc hbit
    unfold layMask at hbit ⊢
    split_ifs at hbit ⊢
    · exact hA c hc hbit
    · exact hB c hc hbit
  rintro ⟨p, hp1, hp2⟩
  apply h
  refine ⟨fun c l => unT k di dj (p (5 * (trI k di dj c).1 + (trI k di dj c).2).toNat l), ?_, ?_⟩
  · intro c l hc hl hbit
    obtain ⟨h1, h2, h3, h4, h5⟩ := hAB l c hc hbit
    exact inCellR_unT k di dj c _ _ _ rfl h1 h3 h4 (hp1 _ l (by omega) hl h5)
  · intro c l c' l' hc hl hc' hl' hne hbit hbit'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hAB l c hc hbit
    obtain ⟨h1', h2', h3', h4', h5'⟩ := hAB l' c' hc' hbit'
    dsimp only
    rw [sqDist_unT]
    refine hp2 _ l _ l' (by omega) hl (by omega) hl' ?_ h5 h5'
    intro heq
    simp only [Prod.mk.injEq] at heq
    apply hne
    have hcc : c = c' := trI_inj k di dj c c' (Prod.ext (by omega) (by omega))
    rw [hcc, heq.2]



/-- Index `5 i + j` of the cell of a half-cell slot. -/
def slotIdx (r : (Fin 5 × Fin 5) × Fin 2) : ℕ := 5 * r.1.1.val + r.1.2.val

/-- The cell `(c / 5, c % 5)` as a pair of `Fin 5`. -/
def cellFin (c : ℕ) : Fin 5 × Fin 5 :=
  (⟨c / 5 % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨c % 5, Nat.mod_lt _ (by norm_num)⟩)

/-- Mask with bit `c` set iff `c < 25` and `c ∈ T`. -/
def maskOf (T : Finset ℕ) : ℕ := Nat.ofBits (fun c : Fin 25 => decide (c.val ∈ T))

theorem maskOf_lt (T : Finset ℕ) : maskOf T < 2 ^ 25 := Nat.ofBits_lt_two_pow _

theorem testBit_maskOf (T : Finset ℕ) (c : ℕ) : (maskOf T).testBit c = true ↔ c < 25 ∧ c ∈ T := by
  unfold maskOf
  by_cases h : c < 25
  · rw [Nat.testBit_ofBits_lt _ _ h]; simp [h]
  · rw [Nat.testBit_ofBits_ge _ _ (by omega)]; simp [h]

theorem filter_maskOf (T : Finset ℕ) (hT : ∀ c ∈ T, c < 25) :
    (Finset.range 25).filter (fun c => (maskOf T).testBit c = true) = T := by
  ext c
  rw [Finset.mem_filter, Finset.mem_range, testBit_maskOf]
  exact ⟨fun h => h.2.2, fun h => ⟨hT c h, hT c h, h⟩⟩

theorem slotIdx_lt (r : (Fin 5 × Fin 5) × Fin 2) : slotIdx r < 25 := by
  unfold slotIdx; omega

theorem slotIdx_cellFin (c : ℕ) (hc : c < 25) (h : Fin 2) : slotIdx (cellFin c, h) = c := by
  unfold slotIdx cellFin; dsimp only; omega

theorem eq_of_slotIdx (r : (Fin 5 × Fin 5) × Fin 2) : r = (cellFin (slotIdx r), r.2) := by
  obtain ⟨⟨i, j⟩, h⟩ := r
  unfold slotIdx cellFin
  refine Prod.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) rfl <;> dsimp only <;> omega

theorem mem_half_image (S : Finset ((Fin 5 × Fin 5) × Fin 2)) (h : Fin 2) (c : ℕ) (hc : c < 25) :
    c ∈ (S.filter (fun r => r.2 = h)).image slotIdx ↔ (cellFin c, h) ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [Finset.mem_filter] at hr
    have := eq_of_slotIdx r
    rw [hr.2] at this
    rw [← this]; exact hr.1
  · intro hm
    exact ⟨(cellFin c, h), Finset.mem_filter.mpr ⟨hm, rfl⟩, slotIdx_cellFin c hc h⟩

theorem card_half_image (S : Finset ((Fin 5 × Fin 5) × Fin 2)) (h : Fin 2) :
    ((S.filter (fun r => r.2 = h)).image slotIdx).card = (S.filter (fun r => r.2 = h)).card := by
  apply Finset.card_image_of_injOn
  intro r hr t ht hrt
  have hr2 : r.2 = h := (Finset.mem_filter.mp hr).2
  have ht2 : t.2 = h := (Finset.mem_filter.mp ht).2
  rw [eq_of_slotIdx r, eq_of_slotIdx t, hrt, hr2, ht2]

theorem inCellR_of_half (r : (Fin 5 × Fin 5) × Fin 2) (P : Point) (c : ℕ) (hc : c < 25)
    (hr : r.1 = cellFin c)
    (h : ((r.1.1.val : ℝ) / 5 ≤ P.1 ∧ P.1 ≤ ((r.1.1.val : ℝ) + 1) / 5) ∧
      ((r.1.2.val : ℝ) / 5 + (r.2.val : ℝ) / 10 ≤ P.2 ∧
       P.2 ≤ (r.1.2.val : ℝ) / 5 + ((r.2.val : ℝ) + 1) / 10)) : InCellR P c := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have e1 : r.1.1.val = c / 5 := by rw [hr]; unfold cellFin; dsimp only; omega
  have e2 : r.1.2.val = c % 5 := by rw [hr]; rfl
  rw [e1] at h1 h2
  rw [e2] at h3 h4
  have g0 : (0 : ℝ) ≤ (r.2.val : ℝ) := Nat.cast_nonneg _
  have g1 : (r.2.val : ℝ) ≤ 1 := by
    have : r.2.val ≤ 1 := by omega
    exact_mod_cast this
  unfold InCellR
  refine ⟨h1, h2, ?_, ?_⟩ <;> linarith

theorem halfbox_of_cover
    (hcov : ∀ A B : ℕ, A < 2 ^ 25 → (∀ c, B.testBit c = true → A.testBit c = true) →
      ((Finset.range 25).filter (fun c => A.testBit c = true)).card +
        ((Finset.range 25).filter (fun c => B.testBit c = true)).card = 25 →
      (∃ c, c < 25 ∧ A.testBit c = false) →
      ∃ a b : ℕ, (∀ c, a.testBit c = true → A.testBit c = true) ∧
        (∀ c, b.testBit c = true → B.testBit c = true) ∧ Infeasible a b)
    (S : Finset ((Fin 5 × Fin 5) × Fin 2)) (q : ((Fin 5 × Fin 5) × Fin 2) → Point)
    (hc : ∀ r ∈ S,
      ((r.1.1.val : ℝ) / 5 ≤ (q r).1 ∧ (q r).1 ≤ ((r.1.1.val : ℝ) + 1) / 5) ∧
      ((r.1.2.val : ℝ) / 5 + (r.2.val : ℝ) / 10 ≤ (q r).2 ∧
       (q r).2 ≤ (r.1.2.val : ℝ) / 5 + ((r.2.val : ℝ) + 1) / 10))
    (hd : ∀ r ∈ S, ∀ t ∈ S, r ≠ t → (1 : ℝ) / 16 < sqDist (q r) (q t))
    (hempty : ∃ c : Fin 5 × Fin 5, ∀ b : Fin 2, (c, b) ∉ S) :
    S.card ≤ 24 := by
  by_contra hcard
  obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq (s := S) (n := 25) (by omega)
  set L : Finset ℕ := (S'.filter (fun r => r.2 = 0)).image slotIdx with hL
  set U : Finset ℕ := (S'.filter (fun r => r.2 = 1)).image slotIdx with hU
  have hLlt : ∀ c ∈ L, c < 25 := by
    intro c hcL; obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hcL; exact slotIdx_lt r
  have hUlt : ∀ c ∈ U, c < 25 := by
    intro c hcU; obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hcU; exact slotIdx_lt r
  have hLm : ∀ c, c < 25 → (c ∈ L ↔ (cellFin c, (0 : Fin 2)) ∈ S') :=
    fun c h => mem_half_image S' 0 c h
  have hUm : ∀ c, c < 25 → (c ∈ U ↔ (cellFin c, (1 : Fin 2)) ∈ S') :=
    fun c h => mem_half_image S' 1 c h
  have hLU : L.card + U.card = 25 := by
    rw [hL, hU, card_half_image, card_half_image, ← hS'c,
      ← Finset.card_filter_add_card_filter_not (s := S') (fun r => r.2 = 0)]
    congr 2
    apply Finset.filter_congr
    intro r _
    omega
  have hAf := filter_maskOf (L ∪ U) (fun c h => (Finset.mem_union.mp h).elim (hLlt c) (hUlt c))
  have hBf := filter_maskOf (L ∩ U) (fun c h => hLlt c (Finset.mem_inter.mp h).1)
  obtain ⟨c0, hc0⟩ := hempty
  obtain ⟨a, b, ha, hb, hinf⟩ := hcov (maskOf (L ∪ U)) (maskOf (L ∩ U)) (maskOf_lt _)
    (by
      intro c h
      rw [testBit_maskOf] at h ⊢
      exact ⟨h.1, Finset.mem_union_left _ (Finset.mem_inter.mp h.2).1⟩)
    (by rw [hAf, hBf, Finset.card_union_add_card_inter, hLU])
    (by
      refine ⟨slotIdx (c0, 0), slotIdx_lt _, ?_⟩
      rw [Bool.eq_false_iff]
      intro h
      rw [testBit_maskOf] at h
      have e0 := eq_of_slotIdx (c0, (0 : Fin 2))
      have e : cellFin (slotIdx (c0, (0 : Fin 2))) = c0 := (congrArg Prod.fst e0).symm
      rcases Finset.mem_union.mp h.2 with h' | h'
      · rw [hLm _ h.1, e] at h'; exact hc0 0 (hS'S h')
      · rw [hUm _ h.1, e] at h'; exact hc0 1 (hS'S h'))
  -- slot of layer `l` in cell `c`
  let sl : ℕ → ℕ → (Fin 5 × Fin 5) × Fin 2 := fun c l =>
    (cellFin c, if l = 0 then (if (cellFin c, (0 : Fin 2)) ∈ S' then 0 else 1) else 1)
  have hsl1 : ∀ c l, (sl c l).1 = cellFin c := fun _ _ => rfl
  have hslm : ∀ c l, c < 25 → l < 2 → (layMask a b l).testBit c = true → sl c l ∈ S' := by
    intro c l hc' hl hbit
    unfold layMask at hbit
    by_cases hl0 : l = 0
    · rw [if_pos hl0] at hbit
      have h1 := ((testBit_maskOf _ _).mp (ha c hbit)).2
      by_cases hm : (cellFin c, (0 : Fin 2)) ∈ S'
      · simp [sl, hl0, hm]
      · have h2 : c ∈ U := (Finset.mem_union.mp h1).resolve_left (fun h => hm ((hLm c hc').mp h))
        simpa [sl, hl0, hm] using (hUm c hc').mp h2
    · rw [if_neg hl0] at hbit
      have h1 := ((testBit_maskOf _ _).mp (hb c hbit)).2
      simpa [sl, hl0] using (hUm c hc').mp (Finset.mem_inter.mp h1).2
  apply hinf
  refine ⟨fun c l => q (sl c l), ?_, ?_⟩
  · intro c l hc' hl hbit
    exact inCellR_of_half (sl c l) _ c hc' (hsl1 c l) (hc _ (hS'S (hslm c l hc' hl hbit)))
  · intro c l c' l' hc' hl hc'' hl' hne hbit hbit'
    refine hd _ (hS'S (hslm c l hc' hl hbit)) _ (hS'S (hslm c' l' hc'' hl' hbit')) ?_
    intro heq
    apply hne
    have e1 : cellFin c = cellFin c' := congrArg Prod.fst heq
    have hcc : c = c' := by
      rw [← slotIdx_cellFin c hc' 0, ← slotIdx_cellFin c' hc'' 0, e1]
    subst hcc
    have e2 : (sl c l).2 = (sl c l').2 := congrArg Prod.snd heq
    by_cases hl0 : l = 0 <;> by_cases hl0' : l' = 0
    · rw [hl0, hl0']
    · exfalso
      unfold layMask at hbit'
      rw [if_neg hl0'] at hbit'
      have h1 := ((testBit_maskOf _ _).mp (hb c hbit')).2
      have hm : (cellFin c, (0 : Fin 2)) ∈ S' := (hLm c hc').mp (Finset.mem_inter.mp h1).1
      simp [sl, hl0, hl0', hm] at e2
    · exfalso
      unfold layMask at hbit
      rw [if_neg hl0] at hbit
      have h1 := ((testBit_maskOf _ _).mp (hb c hbit)).2
      have hm : (cellFin c, (0 : Fin 2)) ∈ S' := (hLm c hc').mp (Finset.mem_inter.mp h1).1
      simp [sl, hl0, hl0', hm] at e2
    · have : l = l' := by omega
      rw [this]


theorem lib_length : nogoods.length = 1584 := by decide +kernel

/-- Every pattern of the library is infeasible. -/
theorem lib_infeasible (e : ℕ) (x : ℕ × ℕ) (hx : nogoods[e]? = some x) : Infeasible x.1 x.2 := by
  have he : e < 1584 := by
    have := (List.getElem?_eq_some_iff.1 hx).1
    rw [lib_length] at this; exact this
  by_cases h1 : e < 95
  · exact twentyfive_nogood_batch1 e (by omega) h1 x hx
  by_cases h2 : e < 198
  · exact twentyfive_nogood_batch2 e (by omega) h2 x hx
  by_cases h3 : e < 387
  · exact twentyfive_nogood_batch3 e (by omega) h3 x hx
  by_cases h4 : e < 604
  · exact twentyfive_nogood_batch4 e (by omega) h4 x hx
  by_cases h5 : e < 1078
  · exact twentyfive_nogood_batch5 e (by omega) h5 x hx
  exact twentyfive_nogood_batch6 e (by omega) he x hx

end HalfboxReduction

open CirclePackingConstants in
theorem solution
    (S : Finset ((Fin 5 × Fin 5) × Fin 2))
    (q : ((Fin 5 × Fin 5) × Fin 2) → Point)
    (hc : ∀ r ∈ S,
      ((r.1.1.val : ℝ) / 5 ≤ (q r).1 ∧
       (q r).1 ≤ ((r.1.1.val : ℝ) + 1) / 5) ∧
      ((r.1.2.val : ℝ) / 5 + (r.2.val : ℝ) / 10 ≤ (q r).2 ∧
       (q r).2 ≤ (r.1.2.val : ℝ) / 5 + ((r.2.val : ℝ) + 1) / 10))
    (hd : ∀ r ∈ S, ∀ t ∈ S, r ≠ t → (1 : ℝ) / 16 < sqDist (q r) (q t))
    (hempty : ∃ c : Fin 5 × Fin 5, ∀ b : Fin 2, (c, b) ∉ S) :
    S.card ≤ 24 := by
  refine HalfboxReduction.halfbox_of_cover ?_ S q hc hd hempty
  intro A B hA hBA hcard hz
  obtain ⟨e, x, k, di, dj, hx, hk, hpa, hpb⟩ := twentyfive_nogood_cover A B hA hBA hcard hz
  exact ⟨A, B, fun _ h => h, fun _ h => h,
    HalfboxReduction.infeasible_transport k di dj x.1 x.2 A B hk (HalfboxReduction.lib_infeasible e x hx) hpa hpb⟩
