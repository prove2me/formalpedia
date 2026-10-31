-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:52:19.819509+00:00
-- url     : https://prove2.me/submissions/8cd8e9be-9f89-4c9f-9992-f76a44d66ea4

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

open FairRentFPTAS.Approx

namespace FRFL7Aux

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



/-- the rounded segment of a bounded piece, as a function of `x`. -/
lemma round_seg (ε : ℝ) (e e' : ℝ × ℝ) (t : List (ℝ × ℝ)) (x : ℝ) :
    PLFun.drop (roundAux ε (e :: e' :: t)) x =
      (roundUp ε e.2 / (1 + ε) * (min (max x e.1) (xStar ε e.1 e'.1 e.2) - e.1) +
        roundUp ε e.2 * (min (max x (xStar ε e.1 e'.1 e.2)) e'.1 - xStar ε e.1 e'.1 e.2)) +
      PLFun.drop (roundAux ε (e' :: t)) x := by
  obtain ⟨s, R', hR'⟩ := roundAux_head ε e' t
  simp only [roundAux]
  rw [hR']
  split_ifs with hxs
  · rw [hxs]
    simp only [List.singleton_append, PLFun.drop]
    rw [min_eq_right (le_max_right x e.1)]
    ring
  · simp only [List.cons_append, List.nil_append, PLFun.drop]
    ring

lemma xStar_id (ε lam x₁ x₂ : ℝ) (hε : 0 < ε) (hlam : 0 < lam) :
    (roundUp ε lam - roundUp ε lam / (1 + ε)) * (xStar ε x₁ x₂ lam - x₁) =
      (roundUp ε lam - lam) * (x₂ - x₁) := by
  have hR := roundUp_pos ε lam hε
  unfold xStar
  field_simp
  ring

lemma round_beyond (ε : ℝ) (hε : 0 < ε) (e e' : ℝ × ℝ) (t : List (ℝ × ℝ)) (he : 0 < e.2)
    (hee : e.1 < e'.1) (x : ℝ) (hx : e'.1 ≤ x) :
    PLFun.drop (roundAux ε (e :: e' :: t)) x = e.2 * (e'.1 - e.1) + PLFun.drop (roundAux ε (e' :: t)) x := by
  rw [round_seg]
  have hxs := xStar_bounds ε e.1 e'.1 e.2 hε he hee
  rw [min_eq_right (le_trans hxs.2.le (le_trans hx (le_max_left _ _))),
    min_eq_right (le_trans hx (le_max_left _ _))]
  have hid := xStar_id ε e.2 e.1 e'.1 hε he
  have : roundUp ε e.2 / (1 + ε) * (xStar ε e.1 e'.1 e.2 - e.1) +
      roundUp ε e.2 * (e'.1 - xStar ε e.1 e'.1 e.2) =
      roundUp ε e.2 * (e'.1 - e.1) -
        (roundUp ε e.2 - roundUp ε e.2 / (1 + ε)) * (xStar ε e.1 e'.1 e.2 - e.1) := by ring
  rw [this, hid]; ring

lemma orig_beyond (e e' : ℝ × ℝ) (t : List (ℝ × ℝ)) (x : ℝ) (hee : e.1 ≤ e'.1) (hx : e'.1 ≤ x) :
    PLFun.drop (e :: e' :: t) x = e.2 * (e'.1 - e.1) + PLFun.drop (e' :: t) x := by
  simp only [PLFun.drop]
  rw [min_eq_right (le_trans hx (le_max_left _ _))]

/-- passing through a prefix of the piece list. -/
lemma prefix_shift (ε : ℝ) (hε : 0 < ε) (e : ℝ × ℝ) (T : List (ℝ × ℝ)) :
    ∀ P : List (ℝ × ℝ), (∀ y ∈ P ++ e :: T, 0 < y.2) →
      ((P ++ e :: T).map Prod.fst).Pairwise (· < ·) →
      ∃ K : ℝ, (∀ x, e.1 ≤ x → PLFun.drop (P ++ e :: T) x = K + PLFun.drop (e :: T) x ∧
        PLFun.drop (roundAux ε (P ++ e :: T)) x = K + PLFun.drop (roundAux ε (e :: T)) x) ∧
        ∀ h, Good h (P ++ e :: T) → Good (h - K) (e :: T) := by
  intro P
  induction P with
  | nil => intro _ _; exact ⟨0, fun x _ => by simp, fun h hg => by simpa using hg⟩
  | cons p P' ih =>
    intro hpos hs
    have hs' : ((P' ++ e :: T).map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp (by simpa using hs)).2
    have hlt : ∀ z ∈ P' ++ e :: T, p.1 < z.1 := fun z hz =>
      (List.pairwise_cons.mp (by simpa using hs)).1 z.1 (List.mem_map_of_mem hz)
    have hpos' : ∀ y ∈ P' ++ e :: T, 0 < y.2 := fun y hy => hpos y (by simp [hy])
    have hp := hpos p (by simp)
    obtain ⟨K', hK', hG'⟩ := ih hpos' hs'
    -- the head of `P' ++ e :: T`
    obtain ⟨q, rest, hq⟩ : ∃ q rest, P' ++ e :: T = q :: rest := by
      cases P' with
      | nil => exact ⟨e, T, rfl⟩
      | cons a b => exact ⟨a, b ++ e :: T, rfl⟩
    have hqe : q.1 ≤ e.1 := by
      cases P' with
      | nil => simp at hq; rw [← hq.1]
      | cons a b =>
        simp at hq
        obtain ⟨rfl, rfl⟩ := hq
        have h2 := hs'
        simp only [List.cons_append, List.map_cons, List.pairwise_cons] at h2
        exact (h2.1 e.1 (by simp)).le
    have hpq : p.1 < q.1 := hlt q (by rw [hq]; simp)
    refine ⟨p.2 * (q.1 - p.1) + K', ?_, ?_⟩
    · intro x hx
      have hqx : q.1 ≤ x := le_trans hqe hx
      obtain ⟨h1, h2⟩ := hK' x hx
      rw [hq] at h1 h2
      simp only [List.cons_append]
      rw [hq]
      rw [orig_beyond p q rest x hpq.le hqx, round_beyond ε hε p q rest hp hpq x hqx, h1, h2]
      constructor <;> ring
    · intro h hg
      simp only [List.cons_append] at hg
      rw [hq] at hg
      simp only [Good] at hg
      have := hG' _ (by rw [hq]; exact hg.2)
      convert this using 1; ring

end FRFL7Aux

open FRFL7Aux in
theorem solution {n : ℕ} (I : Instance n) (ε : ℝ) (hI : Standing I) (hε : 0 < ε) (hε1 : ε < 1)
    (a r : Fin n) (e e' : ℝ × ℝ) (hpiece : [e, e'] <:+: (refineZero (I.v a r)).pieces) :
    (∀ x, e.1 ≤ x → x ≤ e'.1 →
      (I.v a r).eval x ≤ ((roundInst ε I).v a r).eval x ∧
      ((roundInst ε I).v a r).eval x ≤ (I.v a r).eval e'.1 + roundUp ε e.2 * (e'.1 - x) ∧
      ((roundInst ε I).v a r).eval x ≤ (I.v a r).eval e.1 - roundUp ε e.2 / (1 + ε) * (x - e.1)) ∧
    (∀ x, e.1 < x → x < e'.1 →
      (0 ≤ ((roundInst ε I).v a r).eval x ↔ 0 ≤ (I.v a r).eval e.1 ∧ 0 ≤ (I.v a r).eval e'.1) ∧
      (((roundInst ε I).v a r).eval x ≤ 0 ↔ (I.v a r).eval e.1 ≤ 0 ∧ (I.v a r).eval e'.1 ≤ 0)) := by
  set f := I.v a r with hf
  set Lr := refineAux f.base f.pieces with hLr
  have hv : (roundInst ε I).v a r = ⟨f.base, roundAux ε Lr⟩ := rfl
  have hRpos : ∀ y ∈ Lr, 0 < y.2 := by
    intro y hy
    obtain ⟨z, hz, _, hz2⟩ := refineAux_mem _ _ (hI a r).2.2.2 y hy
    rw [hz2]; exact (hI a r).2.2.2 z hz
  have hRs : (Lr.map Prod.fst).Pairwise (· < ·) := refineAux_sorted _ _ (hI a r).2.2.2 (hI a r).2.2.1
  have hgood : Good f.base Lr := refineAux_good _ _ (hI a r).2.2.2
  obtain ⟨P, S, hPS⟩ := hpiece
  change P ++ [e, e'] ++ S = Lr at hPS
  have hL : Lr = P ++ e :: e' :: S := by rw [← hPS]; simp
  rw [hL] at hRpos hRs hgood
  obtain ⟨K, hK, hG⟩ := prefix_shift ε hε e (e' :: S) P hRpos hRs
  have hG2 := hG _ hgood
  simp only [Good] at hG2
  obtain ⟨hsign, _⟩ := hG2
  -- local facts
  have hsub : ∀ y ∈ e :: e' :: S, y ∈ P ++ e :: e' :: S := fun y hy => by simp [hy]
  have hs2 : ((e :: e' :: S).map Prod.fst).Pairwise (· < ·) :=
    List.Pairwise.sublist ((List.sublist_append_right P _).map _) hRs
  have hee' : e.1 < e'.1 := (List.pairwise_cons.mp hs2).1 e'.1 (by simp)
  have hs3 : ((e' :: S).map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs2).2
  have he := hRpos e (by simp)
  have hpos3 : ∀ y ∈ e' :: S, 0 < y.2 := fun y hy => hRpos y (by simp [hy])
  -- all starts are nonnegative, so `e.1 ≥ 0`
  have hst : ∀ y ∈ Lr, 0 ≤ y.1 := by
    intro y hy
    obtain ⟨z, hz, hz1, _⟩ := refineAux_mem _ _ (hI a r).2.2.2 y hy
    exact le_trans (starts_nonneg f (hI a r) z hz) hz1
  have he0 : 0 ≤ e.1 := hst e (by rw [hL]; simp)
  -- the original and rounded values on the piece
  have hvx : ∀ x, 0 ≤ x → f.eval x = f.base - PLFun.drop Lr x := by
    intro x hx
    unfold PLFun.eval; rw [if_neg (not_lt.mpr hx), hLr, refineAux_drop _ _ (hI a r).2.2.2]
  have hwx : ∀ x, 0 ≤ x → ((roundInst ε I).v a r).eval x = f.base - PLFun.drop (roundAux ε Lr) x := by
    intro x hx; rw [hv]; unfold PLFun.eval; rw [if_neg (not_lt.mpr hx)]
  have hRS : ∀ y ∈ roundAux ε (e' :: S), e'.1 ≤ y.1 := by
    intro y hy
    obtain ⟨z, hz, hz1, _⟩ := roundAux_mem ε hε (e' :: S) hpos3 hs3 y hy
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hz1
    · linarith [(List.pairwise_cons.mp hs3).1 z.1 (List.mem_map_of_mem hz)]
  set R := roundUp ε e.2 with hRdef
  obtain ⟨hR1, hR2⟩ := roundUp_bounds ε e.2 hε he
  set Lz := e'.1 - e.1 with hLz
  have hLz0 : 0 < Lz := by rw [hLz]; linarith
  set zs := xStar ε e.1 e'.1 e.2 - e.1 with hzs
  have hxsb := xStar_bounds ε e.1 e'.1 e.2 hε he hee'
  have hzs0 : 0 ≤ zs := by rw [hzs]; linarith
  have hzsL : zs ≤ Lz := by rw [hzs, hLz]; linarith
  have hid : (R - R / (1 + ε)) * zs = (R - e.2) * Lz := xStar_id ε e.2 e.1 e'.1 hε he
  set H := f.base - K with hH
  -- formulas on [e.1, e'.1]
  have hform : ∀ x, e.1 ≤ x → x ≤ e'.1 →
      f.eval x = H - e.2 * (x - e.1) ∧
      ((roundInst ε I).v a r).eval x =
        H - (R / (1 + ε) * min (x - e.1) zs + R * (max (x - e.1) zs - zs)) := by
    intro x hx1 hx2
    have hx0 : 0 ≤ x := le_trans he0 hx1
    obtain ⟨k1, k2⟩ := hK x hx1
    have hd1 : PLFun.drop (e' :: S) x = 0 :=
      drop_eq_zero x (e' :: S) hs3 (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx2
        · linarith [(List.pairwise_cons.mp hs3).1 y.1 (List.mem_map_of_mem hy)])
    have hd2 : PLFun.drop (roundAux ε (e' :: S)) x = 0 :=
      drop_eq_zero x _ (roundAux_sorted ε hε _ hpos3 hs3) (fun y hy => le_trans hx2 (hRS y hy))
    constructor
    · rw [hvx x hx0, hL, k1]
      simp only [PLFun.drop]
      rw [hd1, max_eq_left hx1, min_eq_left hx2, hH]; ring
    · rw [hwx x hx0, hL, k2, round_seg, hd2, max_eq_left hx1]
      have e1 : min x (xStar ε e.1 e'.1 e.2) - e.1 = min (x - e.1) zs := by
        rw [hzs]
        rcases le_total x (xStar ε e.1 e'.1 e.2) with h' | h'
        · rw [min_eq_left h', min_eq_left (by linarith)]
        · rw [min_eq_right h', min_eq_right (by linarith)]
      have e2 : min (max x (xStar ε e.1 e'.1 e.2)) e'.1 - xStar ε e.1 e'.1 e.2 =
          max (x - e.1) zs - zs := by
        have : max x (xStar ε e.1 e'.1 e.2) ≤ e'.1 := max_le hx2 hxsb.2.le
        rw [min_eq_left this, hzs]
        rcases le_total x (xStar ε e.1 e'.1 e.2) with h' | h'
        · rw [max_eq_right h', max_eq_right (by linarith)]; ring
        · rw [max_eq_left h', max_eq_left (by linarith)]; ring
      rw [e1, e2, hH]; ring
  have hHe : f.eval e.1 = H := by
    have := (hform e.1 le_rfl hee'.le).1; rw [this]; ring
  have hBe : f.eval e'.1 = H - e.2 * Lz := (hform e'.1 hee'.le le_rfl).1
  -- ρ bounds
  have hA0 : R / (1 + ε) ≤ e.2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hρ : ∀ z, 0 ≤ z → z ≤ Lz →
      R / (1 + ε) * z ≤ R / (1 + ε) * min z zs + R * (max z zs - zs) ∧
      R / (1 + ε) * min z zs + R * (max z zs - zs) ≤ e.2 * z ∧
      e.2 * Lz - R * (Lz - z) ≤ R / (1 + ε) * min z zs + R * (max z zs - zs) := by
    intro z hz0 hzL
    have hAR : R / (1 + ε) ≤ R := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [roundUp_pos ε e.2 hε]
    rcases le_total z zs with h' | h'
    · rw [min_eq_left h', max_eq_right h', sub_self, mul_zero, add_zero]
      refine ⟨le_rfl, mul_le_mul_of_nonneg_right hA0 hz0, ?_⟩
      have : (R - R / (1 + ε)) * z ≤ (R - R / (1 + ε)) * zs :=
        mul_le_mul_of_nonneg_left h' (by linarith)
      nlinarith
    · rw [min_eq_right h', max_eq_left h']
      refine ⟨?_, ?_, ?_⟩
      · have : R / (1 + ε) * (z - zs) ≤ R * (z - zs) :=
          mul_le_mul_of_nonneg_right hAR (by linarith)
        nlinarith
      · have : (R - e.2) * z ≤ (R - e.2) * Lz := mul_le_mul_of_nonneg_left hzL (by linarith)
        nlinarith
      · nlinarith
  refine ⟨?_, ?_⟩
  · intro x hx1 hx2
    obtain ⟨hv1, hw1⟩ := hform x hx1 hx2
    obtain ⟨b1, b2, b3⟩ := hρ (x - e.1) (by linarith) (by rw [hLz]; linarith)
    rw [hv1, hw1, hHe, hBe]
    refine ⟨by linarith, ?_, by linarith⟩
    have : R * (e'.1 - x) = R * (Lz - (x - e.1)) := by rw [hLz]; ring
    rw [this]; linarith
  · intro x hx1 hx2
    obtain ⟨hv1, hw1⟩ := hform x hx1.le hx2.le
    obtain ⟨b1, b2, b3⟩ := hρ (x - e.1) (by linarith) (by rw [hLz]; linarith)
    rw [hw1, hHe, hBe]
    have hz : 0 < x - e.1 := by linarith
    have hzL : x - e.1 < Lz := by rw [hLz]; linarith
    have hApos : 0 < R / (1 + ε) := div_pos (roundUp_pos ε e.2 hε) (by linarith)
    have hsign' : H ≤ 0 ∨ 0 ≤ H - e.2 * Lz := by
      by_contra hc; push_neg at hc; exact hsign ⟨hc.1, hc.2⟩
    have hlz : e.2 * (x - e.1) < e.2 * Lz := mul_lt_mul_of_pos_left hzL he
    have hAz : 0 < R / (1 + ε) * (x - e.1) := mul_pos hApos hz
    rcases hsign' with hh | hh
    · -- rounded value is negative inside
      have hneg : H - (R / (1 + ε) * min (x - e.1) zs + R * (max (x - e.1) zs - zs)) < 0 := by
        linarith only [hh, b1, hAz]
      have hLpos : 0 < e.2 * Lz := mul_pos he hLz0
      constructor
      · constructor
        · intro h0; linarith only [h0, hneg]
        · rintro ⟨h1, h2⟩
          linarith only [h1, h2, hh, hLpos]
      · constructor
        · intro _; exact ⟨hh, by linarith only [hh, hLpos]⟩
        · intro _; exact hneg.le
    · -- rounded value is positive inside
      have hpos : 0 < H - (R / (1 + ε) * min (x - e.1) zs + R * (max (x - e.1) zs - zs)) := by
        linarith only [hh, b2, hlz]
      have hLpos : 0 < e.2 * Lz := mul_pos he hLz0
      have hH0 : 0 < H := by linarith only [hh, hLpos]
      constructor
      · constructor
        · intro _; exact ⟨hH0.le, hh⟩
        · intro _; exact hpos.le
      · constructor
        · intro h0; linarith only [h0, hpos]
        · rintro ⟨h1, _⟩; linarith only [h1, hH0]
