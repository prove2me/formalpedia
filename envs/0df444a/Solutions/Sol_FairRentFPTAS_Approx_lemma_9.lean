-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:46:23.662607+00:00
-- url     : https://prove2.me/submissions/a0539197-5430-4363-b266-70db8d1cd332

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

open FairRentFPTAS.Approx

namespace FRFL9Aux

/-- `drop` vanishes at a point below every start of a sorted list. -/
lemma drop_eq_zero (x : ℝ) : ∀ (l : List (ℝ × ℝ)), (l.map Prod.fst).Pairwise (· < ·) →
    (∀ e ∈ l, x ≤ e.1) → PLFun.drop l x = 0 := by
  intro l
  induction l with
  | nil => intro _ _; simp [PLFun.drop]
  | cons e t ih =>
    intro hs hx
    cases t with
    | nil =>
      have := hx e (by simp)
      simp [PLFun.drop, max_eq_right this]
    | cons e' t' =>
      have hs' : ((e' :: t').map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
      have hee' : e.1 < e'.1 := (List.pairwise_cons.mp hs).1 e'.1 (by simp)
      have := hx e (by simp)
      simp only [PLFun.drop]
      rw [ih hs' (fun y hy => hx y (List.mem_cons_of_mem _ hy)), max_eq_right this,
        min_eq_left hee'.le]
      ring

lemma starts_nonneg (f : PLFun) (hf : f.WF) : ∀ e ∈ f.pieces, 0 ≤ e.1 := by
  obtain ⟨hne, hhead, hsort, _⟩ := hf
  cases h : f.pieces with
  | nil => exact absurd h hne
  | cons e t =>
    rw [h] at hhead hsort
    simp at hhead
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [hhead]
    · have := (List.pairwise_cons.mp (by simpa using hsort)).1 y.1 (List.mem_map_of_mem hy)
      rw [hhead] at this; exact this.le

lemma eval_zero (f : PLFun) (hf : f.WF) : f.eval 0 = f.base := by
  unfold PLFun.eval
  simp only [lt_irrefl, if_false]
  rw [drop_eq_zero 0 _ hf.2.2.1 (starts_nonneg f hf)]; ring

lemma firstSlope_pos (f : PLFun) (hf : f.WF) : 0 < f.firstSlope := by
  unfold PLFun.firstSlope
  cases h : f.pieces with
  | nil => exact absurd h hf.1
  | cons e t =>
    simp only [List.headD_cons]
    exact hf.2.2.2 e (by rw [h]; simp)

/-! ### the rounded slope -/

lemma roundUp_pos (ε l : ℝ) (hε : 0 < ε) : 0 < roundUp ε l := by
  unfold roundUp; have : (0 : ℝ) < 1 + ε := by linarith
  positivity

lemma roundUp_bounds (ε l : ℝ) (hε : 0 < ε) (hl : 0 < l) :
    l ≤ roundUp ε l ∧ roundUp ε l < (1 + ε) * l := by
  have h1 : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hR := roundUp_pos ε l hε
  set y := Real.logb (1 + ε) l with hy
  have hyl : y * Real.log (1 + ε) = Real.log l := by
    rw [hy, Real.logb, div_mul_cancel₀ _ (ne_of_gt h1)]
  have hlogR : Real.log (roundUp ε l) = (⌈y⌉ : ℝ) * Real.log (1 + ε) := by
    unfold roundUp; rw [Real.log_zpow]
  have c1 := Int.le_ceil y
  have c2 := Int.ceil_lt_add_one y
  constructor
  · rw [← Real.log_le_log_iff hl hR, hlogR, ← hyl]
    exact mul_le_mul_of_nonneg_right c1 h1.le
  · rw [← Real.log_lt_log_iff hR (by positivity), hlogR, Real.log_mul (by linarith) hl.ne', ← hyl]
    nlinarith

lemma roundUp_pow (ε l : ℝ) : ∃ k : ℤ, roundUp ε l = (1 + ε) ^ k := ⟨_, rfl⟩

lemma roundUp_div_pow (ε l : ℝ) (hε : 0 < ε) : ∃ k : ℤ, roundUp ε l / (1 + ε) = (1 + ε) ^ k := by
  refine ⟨⌈Real.logb (1 + ε) l⌉ - 1, ?_⟩
  unfold roundUp
  rw [zpow_sub₀ (by linarith), zpow_one]

/-! ### zero refinement -/

lemma refineAux_head (h : ℝ) (e : ℝ × ℝ) (t : List (ℝ × ℝ)) :
    ∃ R, refineAux h (e :: t) = e :: R := by
  cases t with
  | nil => simp only [refineAux]; split_ifs <;> simp
  | cons e' t' => simp only [refineAux]; split_ifs <;> simp

lemma refineAux_mem (h : ℝ) (l : List (ℝ × ℝ)) (hpos : ∀ e ∈ l, 0 < e.2) :
    ∀ x ∈ refineAux h l, ∃ y ∈ l, y.1 ≤ x.1 ∧ x.2 = y.2 := by
  induction l generalizing h with
  | nil => simp [refineAux]
  | cons e t ih =>
    have he := hpos e (by simp)
    cases t with
    | nil =>
      simp only [refineAux]
      split_ifs with hh
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨x, by simp, le_rfl, rfl⟩
        · refine ⟨e, by simp, ?_, rfl⟩
          have : 0 ≤ h / e.2 := (div_pos hh he).le
          simp only; linarith
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx; exact ⟨x, by simp, le_rfl, rfl⟩
    | cons e' t' =>
      simp only [refineAux]
      have ih' := ih (h - e.2 * (e'.1 - e.1)) (fun z hz => hpos z (List.mem_cons_of_mem _ hz))
      split_ifs with hh
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact ⟨x, by simp, le_rfl, rfl⟩
        · refine ⟨e, by simp, ?_, rfl⟩
          have : 0 ≤ h / e.2 := (div_pos hh.1 he).le
          simp only; linarith
        · obtain ⟨y, hy, hy1, hy2⟩ := ih' x (by simpa using hx)
          exact ⟨y, List.mem_cons_of_mem _ hy, hy1, hy2⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨x, by simp, le_rfl, rfl⟩
        · obtain ⟨y, hy, hy1, hy2⟩ := ih' x (by simpa using hx)
          exact ⟨y, List.mem_cons_of_mem _ hy, hy1, hy2⟩

lemma refineAux_sorted (h : ℝ) (l : List (ℝ × ℝ)) (hpos : ∀ e ∈ l, 0 < e.2)
    (hs : (l.map Prod.fst).Pairwise (· < ·)) :
    ((refineAux h l).map Prod.fst).Pairwise (· < ·) := by
  induction l generalizing h with
  | nil => simp [refineAux]
  | cons e t ih =>
    have he := hpos e (by simp)
    have hs' : (t.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
    have hlt : ∀ z ∈ t, e.1 < z.1 := fun z hz =>
      (List.pairwise_cons.mp hs).1 z.1 (List.mem_map_of_mem hz)
    cases t with
    | nil =>
      simp only [refineAux]
      split_ifs with hh
      · have : 0 < h / e.2 := div_pos hh he
        simp; linarith
      · simp
    | cons e' t' =>
      have hpos' : ∀ z ∈ e' :: t', 0 < z.2 := fun z hz => hpos z (List.mem_cons_of_mem _ hz)
      have IH := ih (h - e.2 * (e'.1 - e.1)) hpos' hs'
      have hmem := refineAux_mem (h - e.2 * (e'.1 - e.1)) (e' :: t') hpos'
      have hge : ∀ x ∈ refineAux (h - e.2 * (e'.1 - e.1)) (e' :: t'), e'.1 ≤ x.1 := by
        intro x hx
        obtain ⟨y, hy, hy1, _⟩ := hmem x hx
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hy1
        · linarith [(List.pairwise_cons.mp hs').1 y.1 (List.mem_map_of_mem hy)]
      have hee' := hlt e' (by simp)
      simp only [refineAux]
      split_ifs with hh
      · have h1 : 0 < h / e.2 := div_pos hh.1 he
        have h2 : h / e.2 < e'.1 - e.1 := by
          rw [div_lt_iff₀ he]; linarith
        simp only [List.map_cons, List.pairwise_cons, List.mem_cons, List.mem_map]
        refine ⟨?_, ?_, IH⟩
        · rintro a (rfl | ⟨x, hx, rfl⟩)
          · linarith
          · linarith [hge x hx]
        · rintro a ⟨x, hx, rfl⟩
          linarith [hge x hx]
      · simp only [List.map_cons, List.pairwise_cons, List.mem_map]
        refine ⟨?_, IH⟩
        rintro a ⟨x, hx, rfl⟩
        linarith [hge x hx]

lemma split_piece (x e1 z e2 : ℝ) (h1 : e1 ≤ z) (h2 : z ≤ e2) :
    (min (max x e1) z - e1) + (min (max x z) e2 - z) = min (max x e1) e2 - e1 := by
  rcases le_total x e1 with hx | hx
  · rw [max_eq_right hx, max_eq_right (le_trans hx h1), min_eq_left h1, min_eq_left (le_trans h1 h2),
      min_eq_left h2]; ring
  rcases le_total x z with hxz | hxz
  · rw [max_eq_left hx, max_eq_right hxz, min_eq_left hxz, min_eq_left h2,
      min_eq_left (le_trans hxz h2)]; ring
  · rw [max_eq_left hx, max_eq_left hxz, min_eq_right hxz]; ring

lemma split_last (x e1 z : ℝ) (h1 : e1 ≤ z) :
    (min (max x e1) z - e1) + (max x z - z) = max x e1 - e1 := by
  rcases le_total x e1 with hx | hx
  · rw [max_eq_right hx, max_eq_right (le_trans hx h1), min_eq_left h1]; ring
  rcases le_total x z with hxz | hxz
  · rw [max_eq_left hx, max_eq_right hxz, min_eq_left hxz]; ring
  · rw [max_eq_left hx, max_eq_left hxz, min_eq_right hxz]; ring

lemma refineAux_drop (h : ℝ) (l : List (ℝ × ℝ)) (hpos : ∀ e ∈ l, 0 < e.2) (x : ℝ) :
    PLFun.drop (refineAux h l) x = PLFun.drop l x := by
  induction l generalizing h with
  | nil => simp [refineAux]
  | cons e t ih =>
    have he := hpos e (by simp)
    cases t with
    | nil =>
      simp only [refineAux]
      split_ifs with hh
      · have : 0 ≤ h / e.2 := (div_pos hh he).le
        simp only [PLFun.drop]
        rw [← mul_add, split_last x e.1 (e.1 + h / e.2) (by linarith)]
      · rfl
    | cons e' t' =>
      have hpos' : ∀ z ∈ e' :: t', 0 < z.2 := fun z hz => hpos z (List.mem_cons_of_mem _ hz)
      have IH := ih (h - e.2 * (e'.1 - e.1)) hpos'
      obtain ⟨R, hR⟩ := refineAux_head (h - e.2 * (e'.1 - e.1)) e' t'
      simp only [refineAux]
      split_ifs with hh
      · have h1 : 0 < h / e.2 := div_pos hh.1 he
        have h2 : h / e.2 < e'.1 - e.1 := by rw [div_lt_iff₀ he]; linarith
        rw [hR]
        rw [hR] at IH
        simp only [PLFun.drop] at IH ⊢
        rw [IH, ← add_assoc, ← mul_add,
          split_piece x e.1 (e.1 + h / e.2) e'.1 (by linarith) (by linarith)]
      · rw [hR]; rw [hR] at IH
        simp only [PLFun.drop] at IH ⊢
        rw [IH]

/-- the sign condition of the refined list, tracking the value `h` at the start. -/
def Good : ℝ → List (ℝ × ℝ) → Prop
  | _, [] => True
  | h, [_] => h ≤ 0
  | h, e :: e' :: t => ¬ (0 < h ∧ h - e.2 * (e'.1 - e.1) < 0) ∧ Good (h - e.2 * (e'.1 - e.1)) (e' :: t)

lemma refineAux_good (h : ℝ) (l : List (ℝ × ℝ)) (hpos : ∀ e ∈ l, 0 < e.2) :
    Good h (refineAux h l) := by
  induction l generalizing h with
  | nil => simp [refineAux, Good]
  | cons e t ih =>
    have he := hpos e (by simp)
    cases t with
    | nil =>
      simp only [refineAux]
      split_ifs with hh
      · simp only [Good]
        have : h - e.2 * (e.1 + h / e.2 - e.1) = 0 := by field_simp; ring
        rw [this]; simp
      · simp only [Good]; linarith
    | cons e' t' =>
      have hpos' : ∀ z ∈ e' :: t', 0 < z.2 := fun z hz => hpos z (List.mem_cons_of_mem _ hz)
      have IH := ih (h - e.2 * (e'.1 - e.1)) hpos'
      obtain ⟨R, hR⟩ := refineAux_head (h - e.2 * (e'.1 - e.1)) e' t'
      simp only [refineAux]
      split_ifs with hh
      · rw [hR]; rw [hR] at IH
        simp only [Good]
        have e1 : h - e.2 * (e.1 + h / e.2 - e.1) = 0 := by field_simp; ring
        have e2 : (0 : ℝ) - e.2 * (e'.1 - (e.1 + h / e.2)) = h - e.2 * (e'.1 - e.1) := by
          field_simp; ring
        rw [e1, e2]
        exact ⟨by simp, by simp, IH⟩
      · rw [hR]; rw [hR] at IH
        simp only [Good]
        exact ⟨hh, IH⟩

/-! ### slope rounding -/

lemma xStar_bounds (ε x₁ x₂ l : ℝ) (hε : 0 < ε) (hl : 0 < l) (hx : x₁ < x₂) :
    x₁ ≤ xStar ε x₁ x₂ l ∧ xStar ε x₁ x₂ l < x₂ := by
  obtain ⟨h1, h2⟩ := roundUp_bounds ε l hε hl
  have hR := roundUp_pos ε l hε
  unfold xStar
  constructor
  · have : 0 ≤ (1 + ε) * (roundUp ε l - l) * (x₂ - x₁) / (ε * roundUp ε l) := by
      apply div_nonneg
      · apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      · positivity
    linarith
  · have : (1 + ε) * (roundUp ε l - l) * (x₂ - x₁) / (ε * roundUp ε l) < x₂ - x₁ := by
      rw [div_lt_iff₀ (by positivity)]
      have hL : 0 < x₂ - x₁ := by linarith
      nlinarith
    linarith

lemma roundAux_head (ε : ℝ) (e : ℝ × ℝ) (t : List (ℝ × ℝ)) :
    ∃ s R, roundAux ε (e :: t) = (e.1, s) :: R := by
  cases t with
  | nil => exact ⟨_, [], rfl⟩
  | cons e' t' =>
    simp only [roundAux]
    split_ifs <;> simp

lemma roundAux_mem (ε : ℝ) (hε : 0 < ε) (l : List (ℝ × ℝ)) (hpos : ∀ e ∈ l, 0 < e.2)
    (hs : (l.map Prod.fst).Pairwise (· < ·)) :
    ∀ x ∈ roundAux ε l, ∃ y ∈ l, y.1 ≤ x.1 ∧
      (x.2 = roundUp ε y.2 ∨ x.2 = roundUp ε y.2 / (1 + ε)) := by
  induction l with
  | nil => simp [roundAux]
  | cons e t ih =>
    have hs' : (t.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
    have hlt : ∀ z ∈ t, e.1 < z.1 := fun z hz =>
      (List.pairwise_cons.mp hs).1 z.1 (List.mem_map_of_mem hz)
    have ih' := ih (fun z hz => hpos z (List.mem_cons_of_mem _ hz)) hs'
    cases t with
    | nil =>
      intro x hx
      simp [roundAux] at hx
      exact ⟨e, by simp, by rw [hx], Or.inr (by rw [hx])⟩
    | cons e' t' =>
      simp only [roundAux]
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · split_ifs at hx with hxs
        · simp at hx; exact ⟨e, by simp, by rw [hx], Or.inl (by rw [hx])⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx
          · exact ⟨e, by simp, by rw [hx], Or.inr (by rw [hx])⟩
          · refine ⟨e, by simp, ?_, Or.inl (by rw [hx])⟩
            rw [hx]
            exact (xStar_bounds ε e.1 e'.1 e.2 hε (hpos e (by simp)) (hlt e' (by simp))).1
      · obtain ⟨y, hy, hy2⟩ := ih' x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hy2⟩

lemma roundAux_sorted (ε : ℝ) (hε : 0 < ε) (l : List (ℝ × ℝ)) (hpos : ∀ e ∈ l, 0 < e.2)
    (hs : (l.map Prod.fst).Pairwise (· < ·)) :
    ((roundAux ε l).map Prod.fst).Pairwise (· < ·) := by
  induction l with
  | nil => simp [roundAux]
  | cons e t ih =>
    have hs' : (t.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
    have hlt : ∀ z ∈ t, e.1 < z.1 := fun z hz =>
      (List.pairwise_cons.mp hs).1 z.1 (List.mem_map_of_mem hz)
    have hpos' : ∀ z ∈ t, 0 < z.2 := fun z hz => hpos z (List.mem_cons_of_mem _ hz)
    have IH := ih hpos' hs'
    cases t with
    | nil => simp [roundAux]
    | cons e' t' =>
      have hmem := roundAux_mem ε hε (e' :: t') hpos' hs'
      have hge : ∀ x ∈ roundAux ε (e' :: t'), e'.1 ≤ x.1 := by
        intro x hx
        obtain ⟨y, hy, hy1, _⟩ := hmem x hx
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hy1
        · linarith [(List.pairwise_cons.mp hs').1 y.1 (List.mem_map_of_mem hy)]
      have hee' := hlt e' (by simp)
      have hxs := xStar_bounds ε e.1 e'.1 e.2 hε (hpos e (by simp)) hee'
      simp only [roundAux]
      rw [List.map_append, List.pairwise_append]
      refine ⟨?_, IH, ?_⟩
      · split_ifs with h
        · simp
        · have hlt' : e.1 < xStar ε e.1 e'.1 e.2 := lt_of_le_of_ne hxs.1 (Ne.symm h)
          simp [hlt']
      · intro a ha b hb
        obtain ⟨xb, hxb, rfl⟩ := List.mem_map.mp hb
        have := hge xb hxb
        split_ifs at ha with h
        · simp at ha; rw [ha]; linarith
        · simp at ha
          rcases ha with rfl | rfl <;> linarith [hxs.2]

/-! ### pointwise comparison -/

/-- the three pointwise inequalities between the original value `v` and the rounded value `w`. -/
def Q (ε v w : ℝ) : Prop := v ≤ w ∧ (0 ≤ v → w ≤ (1 + ε) * v) ∧ (v < 0 → (1 + ε) * w ≤ v)

lemma Q_refl (ε v : ℝ) (hε : 0 < ε) : Q ε v v := by
  refine ⟨le_rfl, fun h => by nlinarith, fun h => by nlinarith⟩

lemma seg_bound (ε lam R h z Lz zs : ℝ) (hε : 0 < ε) (hlam : 0 < lam) (hR1 : lam ≤ R)
    (hR2 : R < (1 + ε) * lam) (hz0 : 0 ≤ z) (hzL : z ≤ Lz) (hzs0 : 0 ≤ zs) (hzsL : zs ≤ Lz)
    (hid : (R - R / (1 + ε)) * zs = (R - lam) * Lz)
    (hsign : ¬ (0 < h ∧ h - lam * Lz < 0)) :
    Q ε (h - lam * z) (h - (R / (1 + ε) * min z zs + R * (max z zs - zs))) := by
  set A := R / (1 + ε) with hA
  have h1e : 0 < 1 + ε := by linarith
  have hAR : A * (1 + ε) = R := by rw [hA]; field_simp
  have hAl : A ≤ lam := by
    rw [hA, div_le_iff₀ h1e]; linarith
  have hA0 : 0 ≤ A := by rw [hA]; apply div_nonneg <;> linarith
  -- ρ in the two regimes
  have hρ : ∀ ρ, ρ = A * min z zs + R * (max z zs - zs) →
      (z ≤ zs → ρ = A * z) ∧ (zs ≤ z → ρ = R * z - (R - lam) * Lz) := by
    intro ρ hρ
    constructor
    · intro hz; rw [hρ, min_eq_left hz, max_eq_right hz]; ring
    · intro hz; rw [hρ, min_eq_right hz, max_eq_left hz]; linarith
  obtain ⟨hρ1, hρ2⟩ := hρ _ rfl
  set ρ := A * min z zs + R * (max z zs - zs) with hρdef
  have hsign' : h ≤ 0 ∨ 0 ≤ h - lam * Lz := by
    by_contra hc; push_neg at hc; exact hsign ⟨hc.1, hc.2⟩
  -- (A)
  have hA_ : ρ ≤ lam * z := by
    rcases le_total z zs with hz | hz
    · rw [hρ1 hz]; exact mul_le_mul_of_nonneg_right hAl hz0
    · rw [hρ2 hz]; nlinarith
  -- lower bound used in (C)
  have hC_ : lam * z ≤ (1 + ε) * ρ := by
    rcases le_total z zs with hz | hz
    · rw [hρ1 hz]
      have : (1 + ε) * (A * z) = R * z := by rw [← hAR]; ring
      rw [this]; exact mul_le_mul_of_nonneg_right hR1 hz0
    · rw [hρ2 hz]
      have : (1 + ε) * (R * z - (R - lam) * Lz) = R * z + (ε * R * z - (1 + ε) * (R - lam) * Lz) := by ring
      rw [this]
      -- (1+ε)(R - lam) Lz = (1+ε)(R - A) zs = ε R zs ≤ ε R z
      have e1 : (1 + ε) * (R - lam) * Lz = ε * R * zs := by
        rw [mul_assoc, ← hid]
        have : (1 + ε) * ((R - A) * zs) = ((1 + ε) * R - A * (1 + ε)) * zs := by ring
        rw [this, hAR]; ring
      rw [e1]
      have : ε * R * zs ≤ ε * R * z := by
        apply mul_le_mul_of_nonneg_left hz; exact mul_nonneg hε.le (by linarith)
      nlinarith
  refine ⟨by linarith, ?_, ?_⟩
  · intro hv
    rcases hsign' with hh | hh
    · have hz : lam * z ≤ 0 := by linarith
      have hz' : z = 0 := by
        have : 0 ≤ lam * z := mul_nonneg hlam.le hz0
        have : lam * z = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · exact h'
      have hρ0 : ρ = 0 := by rw [hρ1 (by rw [hz']; exact hzs0), hz']; ring
      rw [hρ0, hz']
      have : h = 0 := by rw [hz'] at hv; linarith
      rw [this]; ring_nf; exact le_rfl
    · -- (1+ε) lam z - ρ ≤ ε lam Lz ≤ ε h
      have key : (1 + ε) * lam * z - ρ ≤ ε * lam * Lz := by
        rcases le_total z zs with hz | hz
        · rw [hρ1 hz]
          -- ((1+ε)lam - A) z ≤ ((1+ε)lam - A) zs = ((1+ε)lam - R) zs + (R - lam) Lz
          have hc : 0 ≤ (1 + ε) * lam - A := by nlinarith
          have h2 : ((1 + ε) * lam - A) * z ≤ ((1 + ε) * lam - A) * zs :=
            mul_le_mul_of_nonneg_left hz hc
          have h3 : ((1 + ε) * lam - R) * zs ≤ ((1 + ε) * lam - R) * Lz :=
            mul_le_mul_of_nonneg_left hzsL (by linarith)
          nlinarith
        · rw [hρ2 hz]
          have h3 : ((1 + ε) * lam - R) * z ≤ ((1 + ε) * lam - R) * Lz :=
            mul_le_mul_of_nonneg_left hzL (by linarith)
          nlinarith
      have : ε * lam * Lz ≤ ε * h := by
        have : lam * Lz ≤ h := by linarith
        nlinarith
      nlinarith
  · intro hv
    rcases hsign' with hh | hh
    · nlinarith
    · exfalso
      have : lam * z ≤ lam * Lz := mul_le_mul_of_nonneg_left hzL hlam.le
      linarith

lemma last_bound (ε lam R h z : ℝ) (hε : 0 < ε) (hlam : 0 < lam) (hR1 : lam ≤ R)
    (hR2 : R < (1 + ε) * lam) (hz0 : 0 ≤ z) (hh : h ≤ 0) :
    Q ε (h - lam * z) (h - R / (1 + ε) * z) := by
  have h1e : 0 < 1 + ε := by linarith
  have hAR : R / (1 + ε) * (1 + ε) = R := by field_simp
  have hAl : R / (1 + ε) ≤ lam := by rw [div_le_iff₀ h1e]; linarith
  refine ⟨?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hAl hz0; linarith
  · intro hv
    have : lam * z = 0 := by
      have : 0 ≤ lam * z := mul_nonneg hlam.le hz0
      linarith
    have hz : z = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact h'
    rw [hz] at hv ⊢
    have : h = 0 := by linarith
    rw [this]; ring_nf; exact le_rfl
  · intro _
    have : (1 + ε) * (h - R / (1 + ε) * z) = (1 + ε) * h - R * z := by
      rw [mul_sub, ← mul_assoc, mul_comm (1 + ε) (R / (1 + ε)), hAR]
    rw [this]
    have := mul_le_mul_of_nonneg_right hR1 hz0
    nlinarith

lemma main_ineq (ε : ℝ) (hε : 0 < ε) : ∀ (L : List (ℝ × ℝ)) (h : ℝ), (∀ e ∈ L, 0 < e.2) →
    (L.map Prod.fst).Pairwise (· < ·) → Good h L →
    ∀ x : ℝ, (∀ e, L.head? = some e → e.1 ≤ x) →
      Q ε (h - PLFun.drop L x) (h - PLFun.drop (roundAux ε L) x) := by
  intro L
  induction L with
  | nil => intro h _ _ _ x _; simp only [roundAux]; exact Q_refl ε _ hε
  | cons e t ih =>
    intro h hpos hs hgood x hx
    have hex : e.1 ≤ x := hx e rfl
    have he := hpos e (by simp)
    obtain ⟨hR1, hR2⟩ := roundUp_bounds ε e.2 hε he
    have hs' : (t.map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
    have hlt : ∀ z ∈ t, e.1 < z.1 := fun z hz =>
      (List.pairwise_cons.mp hs).1 z.1 (List.mem_map_of_mem hz)
    have hpos' : ∀ z ∈ t, 0 < z.2 := fun z hz => hpos z (List.mem_cons_of_mem _ hz)
    cases t with
    | nil =>
      simp only [Good] at hgood
      simp only [roundAux, PLFun.drop]
      rw [max_eq_left hex]
      have := last_bound ε e.2 (roundUp ε e.2) h (x - e.1) hε he hR1 hR2 (by linarith) hgood
      convert this using 2
    | cons e' t' =>
      simp only [Good] at hgood
      obtain ⟨hsign, hgood'⟩ := hgood
      have hee' := hlt e' (by simp)
      set R := roundUp ε e.2 with hRdef
      have hRpos : 0 < R := roundUp_pos ε e.2 hε
      obtain ⟨s, R', hR'⟩ := roundAux_head ε e' t'
      have hRsorted := roundAux_sorted ε hε (e' :: t') hpos' hs'
      have hRmem := roundAux_mem ε hε (e' :: t') hpos' hs'
      have hRge : ∀ y ∈ roundAux ε (e' :: t'), e'.1 ≤ y.1 := by
        intro y hy
        obtain ⟨z, hz, hz1, _⟩ := hRmem y hy
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hz1
        · linarith [(List.pairwise_cons.mp hs').1 z.1 (List.mem_map_of_mem hz)]
      set Lz := e'.1 - e.1 with hLz
      have hLz0 : 0 < Lz := by rw [hLz]; linarith
      set zs := xStar ε e.1 e'.1 e.2 - e.1 with hzs
      have hxsb := xStar_bounds ε e.1 e'.1 e.2 hε he hee'
      have hzs0 : 0 ≤ zs := by rw [hzs]; linarith
      have hzsL : zs ≤ Lz := by rw [hzs, hLz]; linarith
      have hid : (R - R / (1 + ε)) * zs = (R - e.2) * Lz := by
        rw [hzs, hLz]; unfold xStar; rw [← hRdef]
        field_simp
        ring
      -- the rounded segment, as a function of `x`
      have hseg : PLFun.drop (roundAux ε (e :: e' :: t')) x =
          (R / (1 + ε) * (min (max x e.1) (e.1 + zs) - e.1) +
            R * (min (max x (e.1 + zs)) e'.1 - (e.1 + zs))) +
          PLFun.drop (roundAux ε (e' :: t')) x := by
        simp only [roundAux]
        rw [hR']
        split_ifs with hxs
        · have hzs' : zs = 0 := by rw [hzs, hxs]; ring
          rw [hzs']
          simp only [List.singleton_append, PLFun.drop, add_zero, ← hRdef]
          rw [min_eq_right (le_max_right x e.1)]
          ring
        · simp only [List.cons_append, List.nil_append, PLFun.drop, ← hRdef]
          rw [show e.1 + zs = xStar ε e.1 e'.1 e.2 by rw [hzs]; ring]
          ring
      rw [hseg]
      simp only [PLFun.drop]
      rcases le_total x e'.1 with hxe' | hxe'
      · -- inside the first piece
        have hd1 : PLFun.drop (e' :: t') x = 0 :=
          drop_eq_zero x (e' :: t') hs' (fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hxe'
            · linarith [(List.pairwise_cons.mp hs').1 y.1 (List.mem_map_of_mem hy)])
        have hd2 : PLFun.drop (roundAux ε (e' :: t')) x = 0 :=
          drop_eq_zero x _ hRsorted (fun y hy => le_trans hxe' (hRge y hy))
        rw [hd1, hd2, max_eq_left hex, min_eq_left hxe']
        set z := x - e.1 with hz
        have hz0 : 0 ≤ z := by rw [hz]; linarith
        have hzL : z ≤ Lz := by rw [hz, hLz]; linarith
        have e1 : min x (e.1 + zs) - e.1 = min z zs := by
          rw [hz]
          rcases le_total x (e.1 + zs) with h' | h'
          · rw [min_eq_left h', min_eq_left (by linarith)]
          · rw [min_eq_right h', min_eq_right (by linarith)]; ring
        have e2 : min (max x (e.1 + zs)) e'.1 - (e.1 + zs) = max z zs - zs := by
          have : max x (e.1 + zs) ≤ e'.1 := max_le hxe' (by rw [hzs]; linarith)
          rw [min_eq_left this, hz]
          rcases le_total x (e.1 + zs) with h' | h'
          · rw [max_eq_right h', max_eq_right (by linarith)]; ring
          · rw [max_eq_left h', max_eq_left (by linarith)]; ring
        rw [e1, e2]
        have := seg_bound ε e.2 R h z Lz zs hε he hR1 hR2 hz0 hzL hzs0 hzsL hid hsign
        convert this using 2 <;> ring
      · -- beyond the first piece
        have e0 : min (max x e.1) e'.1 = e'.1 := min_eq_right (le_trans hxe' (le_max_left _ _))
        have e1 : min (max x e.1) (e.1 + zs) = e.1 + zs :=
          min_eq_right (le_trans (by rw [hzs]; linarith) (le_max_left _ _))
        have e2 : min (max x (e.1 + zs)) e'.1 = e'.1 :=
          min_eq_right (le_trans hxe' (le_max_left _ _))
        rw [e0, e1, e2]
        have hfull : R / (1 + ε) * (e.1 + zs - e.1) + R * (e'.1 - (e.1 + zs)) = e.2 * (e'.1 - e.1) := by
          have : R / (1 + ε) * (e.1 + zs - e.1) + R * (e'.1 - (e.1 + zs)) =
              R * Lz - (R - R / (1 + ε)) * zs := by rw [hLz]; ring
          rw [this, hid, hLz]; ring
        rw [hfull]
        have IH := ih (h - e.2 * (e'.1 - e.1)) hpos' hs' hgood' x (fun y hy => by
          simp at hy; rw [← hy]; exact hxe')
        convert IH using 1 <;> ring

end FRFL9Aux

open FRFL9Aux in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (hI : Standing I) (hε : 0 < ε) (hε1 : ε < 1) :
    Standing (roundInst ε I) ∧ PowersProp ε (roundInst ε I) ∧
      ∀ (π : Equiv.Perm (Fin n)) (p : Fin n → ℝ), (∀ r, 0 ≤ p r) →
        IsEF (roundInst ε I) π p → IsEpsEF I ε π p := by
  have hv : ∀ a r, (roundInst ε I).v a r =
      ⟨(I.v a r).base, roundAux ε (refineAux (I.v a r).base (I.v a r).pieces)⟩ := fun a r => rfl
  -- facts about the refined list
  have hRpos : ∀ a r, ∀ e ∈ refineAux (I.v a r).base (I.v a r).pieces, 0 < e.2 := by
    intro a r e he
    obtain ⟨y, hy, _, hy2⟩ := refineAux_mem _ _ (hI a r).2.2.2 e he
    rw [hy2]; exact (hI a r).2.2.2 y hy
  have hRs : ∀ a r, ((refineAux (I.v a r).base (I.v a r).pieces).map Prod.fst).Pairwise (· < ·) :=
    fun a r => refineAux_sorted _ _ (hI a r).2.2.2 (hI a r).2.2.1
  have hhead : ∀ a r, ∃ e R, (I.v a r).pieces = e :: R ∧ e.1 = 0 := by
    intro a r
    obtain ⟨hne, hh, _, _⟩ := hI a r
    cases h : (I.v a r).pieces with
    | nil => exact absurd h hne
    | cons e t => rw [h] at hh; simp at hh; exact ⟨e, t, rfl, hh⟩
  -- pointwise comparison
  have hQ : ∀ a r x, 0 ≤ x → Q ε ((I.v a r).eval x) (((roundInst ε I).v a r).eval x) := by
    intro a r x hx
    rw [hv]
    unfold PLFun.eval
    simp only [if_neg (not_lt.mpr hx)]
    rw [← refineAux_drop (I.v a r).base (I.v a r).pieces (hI a r).2.2.2 x]
    apply main_ineq ε hε _ _ (hRpos a r) (hRs a r)
      (refineAux_good _ _ (hI a r).2.2.2)
    intro e he
    obtain ⟨e0, R, hR, he0⟩ := hhead a r
    obtain ⟨R2, hR2⟩ := refineAux_head (I.v a r).base e0 R
    rw [hR, hR2] at he
    simp at he
    rw [← he, he0]; exact hx
  refine ⟨?_, ?_, ?_⟩
  · intro a r
    rw [hv]
    obtain ⟨e0, R, hR, he0⟩ := hhead a r
    obtain ⟨R2, hR2⟩ := refineAux_head (I.v a r).base e0 R
    obtain ⟨s, R3, hR3⟩ := roundAux_head ε e0 R2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only; rw [hR, hR2, hR3]; simp
    · simp only; rw [hR, hR2, hR3]; simp [he0]
    · exact roundAux_sorted ε hε _ (hRpos a r) (hRs a r)
    · intro e he
      obtain ⟨y, hy, _, hy2⟩ := roundAux_mem ε hε _ (hRpos a r) (hRs a r) e he
      have hy0 := hRpos a r y hy
      rcases hy2 with h' | h'
      · rw [h']; exact roundUp_pos ε _ hε
      · rw [h']; exact div_pos (roundUp_pos ε _ hε) (by linarith)
  · intro a r e he
    rw [hv] at he
    obtain ⟨y, hy, _, hy2⟩ := roundAux_mem ε hε _ (hRpos a r) (hRs a r) e he
    rcases hy2 with h' | h'
    · rw [h']; exact roundUp_pow ε _
    · rw [h']; exact roundUp_div_pow ε _ hε
  · intro π p hp hEF a
    obtain ⟨hA1, hB1, hC1⟩ := hQ a (π a) (p (π a)) (hp _)
    constructor
    · intro hu r
      obtain ⟨hA, _, _⟩ := hQ a r (p r) (hp r)
      have := hEF a r
      have := hB1 hu
      linarith
    · intro hu r
      obtain ⟨hA, _, _⟩ := hQ a r (p r) (hp r)
      have h1 := hEF a r
      have h2 := hC1 hu
      have h3 : (1 + ε) * (I.v a r).eval (p r) ≤ (1 + ε) * ((roundInst ε I).v a r).eval (p r) :=
        mul_le_mul_of_nonneg_left hA (by linarith)
      have h4 : (1 + ε) * ((roundInst ε I).v a r).eval (p r) ≤
          (1 + ε) * ((roundInst ε I).v a (π a)).eval (p (π a)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      linarith
