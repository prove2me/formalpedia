-- Prove2me | solution 1 for BitcoinFeerateDiagram.diagram_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:14:37.450988+00:00
-- url     : https://prove2.me/submissions/c90d4d00-1d14-4d46-bb9f-841401baf7c0

import Definitions.Def_BitcoinFeerateDiagram

open BitcoinFeerateDiagram BitcoinReplacement

private theorem add_fee (a b : FeeFrac) : (a + b).fee = a.fee + b.fee := rfl

private theorem add_size (a b : FeeFrac) : (a + b).size = a.size + b.size := rfl

private theorem sub_fee (a b : FeeFrac) : (a - b).fee = a.fee - b.fee := rfl

private theorem sub_size (a b : FeeFrac) : (a - b).size = a.size - b.size := rfl

private theorem zero_fee : (0 : FeeFrac).fee = 0 := rfl

private theorem zero_size : (0 : FeeFrac).size = 0 := rfl

private theorem ff_ext {x y : FeeFrac} (h1 : x.fee = y.fee) (h2 : x.size = y.size) : x = y := by
  cases x; cases y; simp_all

private theorem add_sub_cancel_ff (c a : FeeFrac) : c + a - a = c :=
  ff_ext (by rw [sub_fee, add_fee]; ring) (by rw [sub_size, add_size]; ring)

private theorem ediv_emod_facts (n d : ℤ) (hd : 0 < d) :
    n % d + d * (n / d) = n ∧ 0 ≤ n % d ∧ n % d < d :=
  (Int.ediv_emod_unique hd).1 ⟨rfl, rfl⟩

private theorem floor_div_int (n d : ℤ) (hd : 0 < d) : ⌊(n : ℚ) / d⌋ = n / d := by
  obtain ⟨h1, h2, h3⟩ := ediv_emod_facts n d hd
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set q := n / d
  set r := n % d
  have hn : (n : ℚ) = r + d * q := by exact_mod_cast h1.symm
  have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast h2
  have hr1 : (r : ℚ) < d := by exact_mod_cast h3
  rw [Int.floor_eq_iff, le_div_iff₀ hd', div_lt_iff₀ hd', hn]
  constructor <;> nlinarith

private theorem ceil_div_int (n d : ℤ) (hd : 0 < d) :
    ⌈(n : ℚ) / d⌉ = n / d + if n % d = 0 then 0 else 1 := by
  obtain ⟨h1, h2, h3⟩ := ediv_emod_facts n d hd
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  set q := n / d
  set r := n % d
  have hn : (n : ℚ) = r + d * q := by exact_mod_cast h1.symm
  have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast h2
  have hr1 : (r : ℚ) < d := by exact_mod_cast h3
  rw [Int.ceil_eq_iff, lt_div_iff₀ hd', div_le_iff₀ hd', hn]
  split_ifs with h0
  · have : (r : ℚ) = 0 := by exact_mod_cast h0
    push_cast
    constructor <;> nlinarith
  · have : (0 : ℚ) < r := by
      have : 0 < r := lt_of_le_of_ne h2 (Ne.symm h0)
      exact_mod_cast this
    push_cast
    constructor <;> nlinarith

private theorem tdiv_tmod_facts (n d : ℤ) (hd : 0 < d) :
    (n.tdiv d = n / d ∧ n.tmod d = n % d) ∨
    (n.tdiv d = n / d + 1 ∧ n.tmod d = n % d - d ∧ n % d ≠ 0) := by
  rw [Int.tdiv_eq_ediv, Int.tmod_eq_emod, Int.sign_eq_one_of_pos hd]
  by_cases hc : 0 ≤ n ∨ d ∣ n
  · left; simp [hc]
  · right
    have hnd : ¬ d ∣ n := fun h => hc (Or.inr h)
    rw [Int.dvd_iff_emod_eq_zero] at hnd
    simp [hc, Int.natAbs_of_nonneg hd.le, hnd]

private theorem sizesPos_cons {c : FeeFrac} {cs : List FeeFrac} (h : SizesPos (c :: cs)) :
    0 < c.size ∧ SizesPos cs :=
  ⟨h c (List.mem_cons_self ..), fun d hd => h d (List.mem_cons_of_mem _ hd)⟩

private theorem sizesPos_nil : SizesPos [] := fun c hc => by simp at hc

private theorem diagram_cons_of_le {c : FeeFrac} {cs : List FeeFrac} {x : ℚ} (hx : x ≤ c.size) :
    diagram (c :: cs) x = c.fee * x / c.size := by
  simp [diagram, hx]

private theorem diagram_zero {cs : List FeeFrac} (h : SizesPos cs) : diagram cs 0 = 0 := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    have hc := (sizesPos_cons h).1
    rw [diagram_cons_of_le (by exact_mod_cast hc.le)]; simp

private theorem diagram_cons_of_ge {c : FeeFrac} {cs : List FeeFrac} (h : SizesPos (c :: cs))
    {x : ℚ} (hx : (c.size : ℚ) ≤ x) : diagram (c :: cs) x = c.fee + diagram cs (x - c.size) := by
  obtain ⟨hc, hcs⟩ := sizesPos_cons h
  have hc' : (c.size : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  rcases hx.lt_or_eq with hlt | heq
  · simp [diagram, not_le.2 hlt]
  · rw [← heq, diagram_cons_of_le le_rfl, sub_self, diagram_zero hcs, mul_div_assoc, div_self hc',
      mul_one, add_zero]

private theorem diagramSize_cons (c : FeeFrac) (cs : List FeeFrac) :
    diagramSize (c :: cs) = c.size + diagramSize cs := by
  simp [diagramSize]

private theorem diagramFee_cons (c : FeeFrac) (cs : List FeeFrac) :
    diagramFee (c :: cs) = c.fee + diagramFee cs := by
  simp [diagramFee]

private theorem diagramSize_nonneg {cs : List FeeFrac} (h : SizesPos cs) : 0 ≤ diagramSize cs := by
  induction cs with
  | nil => simp [diagramSize]
  | cons c cs ih =>
    obtain ⟨hc, hcs⟩ := sizesPos_cons h
    rw [diagramSize_cons]; linarith [ih hcs]

/-- The diagram starts at `(0, 0)`. -/
theorem solution {cs : List FeeFrac} (h : SizesPos cs) :
    diagram cs 0 = 0 := by
  exact diagram_zero h
