-- Prove2me | solution 1 for BitcoinFeerateDiagram.improves_total_fee_not_strict
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:14:39.497659+00:00
-- url     : https://prove2.me/submissions/e8d5f071-d80c-4051-9ca6-877098a5437f

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

/-- `seg acc rem x = accum.fee + diagram rem (x - accum.size)`: the diagram of the whole input, for
`x ≥ accum.size`, expressed through the unprocessed chunks `rem`. -/
private def seg (acc : FeeFrac) (rem : List FeeFrac) (x : ℚ) : ℚ :=
  acc.fee + diagram rem (x - acc.size)

private theorem seg_nil (acc : FeeFrac) (x : ℚ) : seg acc [] x = acc.fee := by
  simp [seg, diagram]

private theorem seg_zero (cs : List FeeFrac) (x : ℚ) : seg 0 cs x = diagram cs x := by
  simp [seg, zero_fee, zero_size]

private theorem seg_cons_of_le {acc c : FeeFrac} {rem : List FeeFrac} {x : ℚ}
    (_h1 : (acc.size : ℚ) ≤ x) (h2 : x ≤ ((c + acc).size : ℚ)) :
    seg acc (c :: rem) x = acc.fee + c.fee * (x - acc.size) / c.size := by
  rw [add_size] at h2; push_cast at h2
  unfold seg; rw [diagram_cons_of_le (by linarith)]

private theorem seg_advance {acc c : FeeFrac} {rem : List FeeFrac} (h : SizesPos (c :: rem)) {x : ℚ}
    (hx : ((c + acc).size : ℚ) ≤ x) : seg (c + acc) rem x = seg acc (c :: rem) x := by
  unfold seg
  rw [add_size] at hx ⊢
  push_cast at hx
  rw [add_fee, diagram_cons_of_ge h (by linarith)]
  have : x - ((c.size + acc.size : ℤ) : ℚ) = x - acc.size - c.size := by push_cast; ring
  rw [this]; push_cast; ring

private theorem seg_at_break {acc c : FeeFrac} {rem : List FeeFrac} (hc : 0 < c.size) :
    seg acc (c :: rem) ((c + acc).size : ℚ) = (c + acc).fee := by
  have hc' : (c.size : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc'' : (0 : ℚ) < c.size := by exact_mod_cast hc
  rw [seg_cons_of_le (by rw [add_size]; push_cast; linarith) le_rfl, add_fee, add_size]
  push_cast
  field_simp
  ring

private theorem seg_affine_cons (acc c : FeeFrac) (rem : List FeeFrac) :
    ∃ α β : ℚ, ∀ x, (acc.size : ℚ) ≤ x → x ≤ ((c + acc).size : ℚ) →
      seg acc (c :: rem) x = α + β * x := by
  refine ⟨acc.fee - c.fee * acc.size / c.size, c.fee / c.size, fun x h1 h2 => ?_⟩
  rw [seg_cons_of_le h1 h2]; ring

private theorem seg_affine_nil (acc : FeeFrac) :
    ∃ α β : ℚ, ∀ x : ℚ, seg acc [] x = α + β * x :=
  ⟨acc.fee, 0, fun x => by rw [seg_nil]; ring⟩

/-- The frontier `max accum[0].size accum[1].size` of the sweep. -/
private def M (acc0 acc1 : FeeFrac) : ℚ := ((max acc0.size acc1.size : ℤ) : ℚ)

private theorem le_M_left (acc0 acc1 : FeeFrac) : (acc0.size : ℚ) ≤ M acc0 acc1 := by
  unfold M; exact_mod_cast le_max_left _ _

private theorem le_M_right (acc0 acc1 : FeeFrac) : (acc1.size : ℚ) ≤ M acc0 acc1 := by
  unfold M; exact_mod_cast le_max_right _ _

private theorem M_le {acc0 acc1 : FeeFrac} {y : ℤ} (h0 : acc0.size ≤ y) (h1 : acc1.size ≤ y) :
    M acc0 acc1 ≤ (y : ℚ) := by
  unfold M; exact_mod_cast max_le h0 h1

private theorem M_eq_left {acc0 acc1 : FeeFrac} (h : acc1.size ≤ acc0.size) :
    M acc0 acc1 = (acc0.size : ℚ) := by
  unfold M; rw [max_eq_left h]

private theorem M_eq_right {acc0 acc1 : FeeFrac} (h : acc0.size ≤ acc1.size) :
    M acc0 acc1 = (acc1.size : ℚ) := by
  unfold M; rw [max_eq_right h]

/-- `ByRatio{P - A} <=> ByRatio{c}` is `greater` iff `P` lies strictly above the line through `A`
with slope `c` (evaluated at `P.size`). -/
private theorem byRatio_sub_gt_iff (P A c : FeeFrac) (hc : 0 < c.size) :
    FeeFrac.byRatioCmp (P - A) c = .gt ↔
      (A.fee : ℚ) + c.fee * (P.size - A.size) / c.size < P.fee := by
  have hc' : (0 : ℚ) < c.size := by exact_mod_cast hc
  unfold FeeFrac.byRatioCmp FeeFrac.mul
  rw [compare_gt_iff_gt, sub_fee, sub_size]
  constructor
  · intro h
    have h' : (c.fee : ℚ) * (P.size - A.size) < (P.fee - A.fee) * c.size := by exact_mod_cast h
    have := (div_lt_iff₀ hc').2 h'
    linarith
  · intro h
    have h' : (c.fee : ℚ) * (P.size - A.size) / c.size < P.fee - A.fee := by linarith
    rw [div_lt_iff₀ hc'] at h'
    exact_mod_cast h'

private theorem byRatio_sub_lt_iff (P A c : FeeFrac) (hc : 0 < c.size) :
    FeeFrac.byRatioCmp (P - A) c = .lt ↔
      (P.fee : ℚ) < A.fee + c.fee * (P.size - A.size) / c.size := by
  have hc' : (0 : ℚ) < c.size := by exact_mod_cast hc
  unfold FeeFrac.byRatioCmp FeeFrac.mul
  rw [compare_lt_iff_lt, sub_fee, sub_size]
  constructor
  · intro h
    have h' : (P.fee - A.fee : ℚ) * c.size < c.fee * (P.size - A.size) := by exact_mod_cast h
    have := (lt_div_iff₀ hc').2 h'
    linarith
  · intro h
    have h' : (P.fee - A.fee : ℚ) < c.fee * (P.size - A.size) / c.size := by linarith
    rw [lt_div_iff₀ hc'] at h'
    exact_mod_cast h'

/-- `Spec o S0 S1`: the `std::partial_ordering` `o` is the one determined by "side 0 is strictly
better somewhere" (`S0`) and "side 1 is strictly better somewhere" (`S1`). -/
private def Spec (o : PartialOrdering) (S0 S1 : Prop) : Prop :=
  match o with
  | .greater => S0 ∧ ¬ S1
  | .less => ¬ S0 ∧ S1
  | .equivalent => ¬ S0 ∧ ¬ S1
  | .unordered => S0 ∧ S1

private theorem Spec_congr {o : PartialOrdering} {S0 S0' S1 S1' : Prop} (h0 : S0 ↔ S0')
    (h1 : S1 ↔ S1') : Spec o S0 S1 ↔ Spec o S0' S1' := by
  cases o <;> simp [Spec, h0, h1]

private theorem Spec_unordered {S0 S1 : Prop} (h0 : S0) (h1 : S1) :
    Spec .unordered S0 S1 :=
  ⟨h0, h1⟩

private theorem Spec_greater_iff {o : PartialOrdering} {S0 S1 : Prop} (h : Spec o S0 S1) :
    o = .greater ↔ S0 ∧ ¬ S1 := by
  cases o <;> simp [Spec] at h ⊢ <;> tauto

private theorem Spec_less_iff {o : PartialOrdering} {S0 S1 : Prop} (h : Spec o S0 S1) :
    o = .less ↔ ¬ S0 ∧ S1 := by
  cases o <;> simp [Spec] at h ⊢ <;> tauto

private theorem Spec_equivalent_iff {o : PartialOrdering} {S0 S1 : Prop} (h : Spec o S0 S1) :
    o = .equivalent ↔ ¬ S0 ∧ ¬ S1 := by
  cases o <;> simp [Spec] at h ⊢ <;> tauto

private theorem Spec_unordered_iff {o : PartialOrdering} {S0 S1 : Prop} (h : Spec o S0 S1) :
    o = .unordered ↔ S0 ∧ S1 := by
  cases o <;> simp [Spec] at h ⊢ <;> tauto

/-- One sweep step for one flag: if `f0 - f1` is affine on `[m, m']`, the flag was correct up to
`m`, and the step records the comparison at `m'`, then the flag is correct up to `m'`. -/
private theorem flag_step {f0 f1 : ℚ → ℚ} {m m' α β : ℚ} (hm : m ≤ m')
    (haff : ∀ x, m ≤ x → x ≤ m' → f0 x - f1 x = α + β * x) {b : Bool}
    (hb : b = false → f0 m ≤ f1 m) :
    (b = true ∨ ∃ x, m ≤ x ∧ f1 x < f0 x) ↔
      ((b || decide (f1 m' < f0 m')) = true ∨ ∃ x, m' ≤ x ∧ f1 x < f0 x) := by
  constructor
  · rintro (hb' | ⟨x, hx, hlt⟩)
    · left; simp [hb']
    · by_cases hx' : m' ≤ x
      · exact Or.inr ⟨x, hx', hlt⟩
      · push Not at hx'
        by_cases hbm : f1 m' < f0 m'
        · left; simp [hbm]
        · push Not at hbm
          cases b with
          | true => left; rfl
          | false =>
            exfalso
            have h0 := hb rfl
            have e1 := haff m le_rfl hm
            have e2 := haff m' hm le_rfl
            have e3 := haff x hx hx'.le
            have key : (m' - m) * (f0 x - f1 x) =
                (m' - x) * (f0 m - f1 m) + (x - m) * (f0 m' - f1 m') := by
              rw [e1, e2, e3]; ring
            have t1 : (m' - x) * (f0 m - f1 m) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
            have t2 : (x - m) * (f0 m' - f1 m') ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
            have t3 : 0 < (m' - m) * (f0 x - f1 x) := mul_pos (by linarith) (by linarith)
            linarith
  · rintro (hb' | ⟨x, hx, hlt⟩)
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hb'
      rcases hb' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨m', hm, h⟩
    · exact Or.inr ⟨x, hm.trans hx, hlt⟩

/-- One full iteration of the sweep, abstractly: the recorded flags after the step together with
the recursive result give the semantic value before the step. -/
private theorem step_partial {f0 f1 : ℚ → ℚ} {m m' α β : ℚ} (hm : m ≤ m')
    (haff : ∀ x, m ≤ x → x ≤ m' → f0 x - f1 x = α + β * x)
    {b0 b1 : Bool} (hb0 : b0 = false → f0 m ≤ f1 m) (hb1 : b1 = false → f1 m ≤ f0 m)
    {b0' b1' : Bool} (h0' : b0' = (b0 || decide (f1 m' < f0 m')))
    (h1' : b1' = (b1 || decide (f0 m' < f1 m'))) {res : PartialOrdering}
    (hres : (b0' && b1') = false →
      Spec res (b0' = true ∨ ∃ x, m' ≤ x ∧ f1 x < f0 x)
               (b1' = true ∨ ∃ x, m' ≤ x ∧ f0 x < f1 x)) :
    Spec (if (b0' && b1') = true then PartialOrdering.unordered else res)
      (b0 = true ∨ ∃ x, m ≤ x ∧ f1 x < f0 x) (b1 = true ∨ ∃ x, m ≤ x ∧ f0 x < f1 x) := by
  have e0 := flag_step hm haff hb0
  have e1 := flag_step (f0 := f1) (f1 := f0) hm (α := -α) (β := -β)
    (fun x h1 h2 => by rw [← neg_sub, haff x h1 h2]; ring) hb1
  rw [← h0'] at e0
  rw [← h1'] at e1
  rw [Spec_congr e0 e1]
  split_ifs with h
  · simp only [Bool.and_eq_true] at h
    exact Spec_unordered (Or.inl h.1) (Or.inl h.2)
  · exact hres (by simpa using h)

private theorem exists_seg_advance_right {acc c : FeeFrac} {rem : List FeeFrac}
    (h : SizesPos (c :: rem)) (g : ℚ → ℚ) {m' : ℚ} (hm' : ((c + acc).size : ℚ) ≤ m') :
    (∃ x, m' ≤ x ∧ g x < seg (c + acc) rem x) ↔ (∃ x, m' ≤ x ∧ g x < seg acc (c :: rem) x) :=
  exists_congr fun x => and_congr_right fun hx => by rw [seg_advance h (hm'.trans hx)]

private theorem exists_seg_advance_left {acc c : FeeFrac} {rem : List FeeFrac}
    (h : SizesPos (c :: rem)) (g : ℚ → ℚ) {m' : ℚ} (hm' : ((c + acc).size : ℚ) ≤ m') :
    (∃ x, m' ≤ x ∧ seg (c + acc) rem x < g x) ↔ (∃ x, m' ≤ x ∧ seg acc (c :: rem) x < g x) :=
  exists_congr fun x => and_congr_right fun hx => by rw [seg_advance h (hm'.trans hx)]

private theorem head?_mem {c : FeeFrac} {cs : List FeeFrac} {d : FeeFrac} (h : d ∈ (c :: cs).head?) :
    d = c := by
  simpa using h.symm

private theorem not_and_of_and_false {b0 b1 : Bool} (h : (b0 && b1) = false) :
    ¬ (b0 = true ∧ b1 = true) := by
  rintro ⟨h0, h1⟩; simp [h0, h1] at h

private theorem M_zero : M 0 0 = 0 := by
  simp [M, zero_size]

/-- The loop invariant of `CompareChunks`: from any reachable state, the result of the remaining
sweep is the partial ordering determined by the flags so far together with the comparison of the
two remaining diagrams beyond the frontier `max accum[0].size accum[1].size`. -/
private theorem sweep_spec (n : ℕ) :
    ∀ (rem0 rem1 : List FeeFrac) (acc0 acc1 : FeeFrac) (b0 b1 : Bool),
    rem0.length + rem1.length = n →
    SizesPos rem0 → SizesPos rem1 →
    (∀ c ∈ rem0.head?, acc1.size < acc0.size + c.size) →
    (∀ c ∈ rem1.head?, acc0.size < acc1.size + c.size) →
    ¬ (b0 = true ∧ b1 = true) →
    (b0 = false → seg acc0 rem0 (M acc0 acc1) ≤ seg acc1 rem1 (M acc0 acc1)) →
    (b1 = false → seg acc1 rem1 (M acc0 acc1) ≤ seg acc0 rem0 (M acc0 acc1)) →
    Spec (sweep rem0 rem1 acc0 acc1 b0 b1)
      (b0 = true ∨ ∃ x, M acc0 acc1 ≤ x ∧ seg acc1 rem1 x < seg acc0 rem0 x)
      (b1 = true ∨ ∃ x, M acc0 acc1 ≤ x ∧ seg acc0 rem0 x < seg acc1 rem1 x) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro rem0 rem1 acc0 acc1 b0 b1 hn h0 h1 H2 H2' hnb H5 H5'
  cases rem0 with
  | nil =>
    cases rem1 with
    | nil =>
      rw [sweep]
      simp only [seg_nil] at H5 H5' ⊢
      cases b0 <;> cases b1
      · have a := H5 rfl
        have b := H5' rfl
        simp only [boolCompare]
        unfold Spec
        refine ⟨?_, ?_⟩
        · rintro (h | ⟨x, -, hx⟩)
          · simp at h
          · linarith
        · rintro (h | ⟨x, -, hx⟩)
          · simp at h
          · linarith
      · have a := H5 rfl
        simp only [boolCompare]
        unfold Spec
        refine ⟨?_, by simp⟩
        rintro (h | ⟨x, -, hx⟩)
        · simp at h
        · linarith
      · have b := H5' rfl
        simp only [boolCompare]
        unfold Spec
        refine ⟨by simp, ?_⟩
        rintro (h | ⟨x, -, hx⟩)
        · simp at h
        · linarith
      · exact absurd ⟨rfl, rfl⟩ hnb
    | cons c1 r1 =>
      -- done_0: side 1 advances, compared against the constant tail of side 0
      simp only [sweep]
      obtain ⟨hc1, hr1⟩ := sizesPos_cons h1
      have hA1 : acc0.size < acc1.size + c1.size := H2' c1 (by simp)
      have hA1' : acc0.size ≤ (c1 + acc1).size := by rw [add_size]; omega
      have hB1' : acc1.size ≤ (c1 + acc1).size := by rw [add_size]; omega
      obtain ⟨α1, β1, haff1⟩ := seg_affine_cons acc1 c1 r1
      obtain ⟨α0, β0, haff0⟩ := seg_affine_nil acc0
      have hm : M acc0 acc1 ≤ ((c1 + acc1).size : ℚ) := M_le hA1' hB1'
      have hf1 : seg acc1 (c1 :: r1) ((c1 + acc1).size : ℚ) = (c1 + acc1).fee := seg_at_break hc1
      have hf0 : seg acc0 [] ((c1 + acc1).size : ℚ) = acc0.fee := seg_nil _ _
      have hgt' : ((c1 + acc1 - acc0).byRatioCmp ⟨0, 1⟩ == .gt) =
          decide (seg acc0 [] ((c1 + acc1).size : ℚ) < seg acc1 (c1 :: r1) ((c1 + acc1).size : ℚ)) := by
        rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_gt_iff _ _ _ (by simp), hf0, hf1]
        simp
      have hlt' : ((c1 + acc1 - acc0).byRatioCmp ⟨0, 1⟩ == .lt) =
          decide (seg acc1 (c1 :: r1) ((c1 + acc1).size : ℚ) < seg acc0 [] ((c1 + acc1).size : ℚ)) := by
        rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_lt_iff _ _ _ (by simp), hf0, hf1]
        simp
      refine step_partial (f0 := seg acc0 []) (f1 := seg acc1 (c1 :: r1)) hm (α := α0 - α1)
        (β := β0 - β1)
        (fun x hx1 hx2 => by rw [haff0 x, haff1 x (le_trans (le_M_right _ _) hx1) hx2]; ring)
        H5 H5' (by rw [hlt']) (by rw [hgt']) ?_
      intro hnb'
      have hM' : M acc0 (c1 + acc1) = ((c1 + acc1).size : ℚ) := M_eq_right hA1'
      have := ih ([].length + r1.length) (by simp at hn ⊢; omega) [] r1 acc0 (c1 + acc1) _ _ rfl
        sizesPos_nil hr1 (by simp)
        (fun c hc => by rw [add_size]; have := hr1 c (List.mem_of_mem_head? hc); omega)
        (not_and_of_and_false hnb')
        (by
          intro hb
          rw [hM', seg_advance h1 le_rfl]
          rw [hlt'] at hb
          simp at hb
          exact hb.2)
        (by
          intro hb
          rw [hM', seg_advance h1 le_rfl]
          rw [hgt'] at hb
          simp at hb
          exact hb.2)
      rw [hM', exists_seg_advance_left h1 (seg acc0 []) le_rfl,
        exists_seg_advance_right h1 (seg acc0 []) le_rfl] at this
      exact this
  | cons c0 r0 =>
    obtain ⟨hc0, hr0⟩ := sizesPos_cons h0
    have hA0 : acc1.size < acc0.size + c0.size := H2 c0 (by simp)
    have hA0' : acc1.size ≤ (c0 + acc0).size := by rw [add_size]; omega
    have hB0' : acc0.size ≤ (c0 + acc0).size := by rw [add_size]; omega
    obtain ⟨α0, β0, haff0⟩ := seg_affine_cons acc0 c0 r0
    cases rem1 with
    | nil =>
      -- done_1: side 0 advances, compared against the constant tail of side 1
      simp only [sweep]
      obtain ⟨α1, β1, haff1⟩ := seg_affine_nil acc1
      have hm : M acc0 acc1 ≤ ((c0 + acc0).size : ℚ) := M_le hB0' hA0'
      have hf0 : seg acc0 (c0 :: r0) ((c0 + acc0).size : ℚ) = (c0 + acc0).fee := seg_at_break hc0
      have hf1 : seg acc1 [] ((c0 + acc0).size : ℚ) = acc1.fee := seg_nil _ _
      have hgt' : ((c0 + acc0 - acc1).byRatioCmp ⟨0, 1⟩ == .gt) =
          decide (seg acc1 [] ((c0 + acc0).size : ℚ) < seg acc0 (c0 :: r0) ((c0 + acc0).size : ℚ)) := by
        rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_gt_iff _ _ _ (by simp), hf0, hf1]
        simp
      have hlt' : ((c0 + acc0 - acc1).byRatioCmp ⟨0, 1⟩ == .lt) =
          decide (seg acc0 (c0 :: r0) ((c0 + acc0).size : ℚ) < seg acc1 [] ((c0 + acc0).size : ℚ)) := by
        rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_lt_iff _ _ _ (by simp), hf0, hf1]
        simp
      refine step_partial (f0 := seg acc0 (c0 :: r0)) (f1 := seg acc1 []) hm (α := α0 - α1)
        (β := β0 - β1)
        (fun x hx1 hx2 => by rw [haff0 x (le_trans (le_M_left _ _) hx1) hx2, haff1 x]; ring)
        H5 H5' (by rw [hgt']) (by rw [hlt']) ?_
      intro hnb'
      have hM' : M (c0 + acc0) acc1 = ((c0 + acc0).size : ℚ) := M_eq_left hA0'
      have := ih (r0.length + [].length) (by simp at hn ⊢; omega) r0 [] (c0 + acc0) acc1 _ _ rfl
        hr0 sizesPos_nil
        (fun c hc => by rw [add_size]; have := hr0 c (List.mem_of_mem_head? hc); omega) (by simp)
        (not_and_of_and_false hnb')
        (by
          intro hb
          rw [hM', seg_advance h0 le_rfl]
          rw [hgt'] at hb
          simp at hb
          exact hb.2)
        (by
          intro hb
          rw [hM', seg_advance h0 le_rfl]
          rw [hlt'] at hb
          simp at hb
          exact hb.2)
      rw [hM', exists_seg_advance_right h0 (seg acc1 []) le_rfl,
        exists_seg_advance_left h0 (seg acc1 []) le_rfl] at this
      exact this
    | cons c1 r1 =>
      simp only [sweep]
      rw [add_sub_cancel_ff, add_sub_cancel_ff]
      obtain ⟨hc1, hr1⟩ := sizesPos_cons h1
      have hA1 : acc0.size < acc1.size + c1.size := H2' c1 (by simp)
      have hA1' : acc0.size ≤ (c1 + acc1).size := by rw [add_size]; omega
      have hB1' : acc1.size ≤ (c1 + acc1).size := by rw [add_size]; omega
      obtain ⟨α1, β1, haff1⟩ := seg_affine_cons acc1 c1 r1
      by_cases hgt : (c0 + acc0).size > (c1 + acc1).size
      · rw [if_pos hgt]
        -- unproc_side = 1: P = c1 + acc1 is compared against the segment [acc0, c0 + acc0]
        have hm : M acc0 acc1 ≤ ((c1 + acc1).size : ℚ) := M_le hA1' hB1'
        have hf1 : seg acc1 (c1 :: r1) ((c1 + acc1).size : ℚ) = (c1 + acc1).fee := seg_at_break hc1
        have hf0 : seg acc0 (c0 :: r0) ((c1 + acc1).size : ℚ) =
            acc0.fee + c0.fee * (((c1 + acc1).size : ℚ) - acc0.size) / c0.size :=
          seg_cons_of_le (by exact_mod_cast hA1') (by exact_mod_cast hgt.le)
        have hgt' : ((c1 + acc1 - acc0).byRatioCmp c0 == .gt) =
            decide (seg acc0 (c0 :: r0) ((c1 + acc1).size : ℚ) <
              seg acc1 (c1 :: r1) ((c1 + acc1).size : ℚ)) := by
          rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_gt_iff _ _ _ hc0, hf0, hf1]
        have hlt' : ((c1 + acc1 - acc0).byRatioCmp c0 == .lt) =
            decide (seg acc1 (c1 :: r1) ((c1 + acc1).size : ℚ) <
              seg acc0 (c0 :: r0) ((c1 + acc1).size : ℚ)) := by
          rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_lt_iff _ _ _ hc0, hf0, hf1]
        refine step_partial (f0 := seg acc0 (c0 :: r0)) (f1 := seg acc1 (c1 :: r1)) hm
          (α := α0 - α1) (β := β0 - β1)
          (fun x hx1 hx2 => by
            rw [haff0 x (le_trans (le_M_left _ _) hx1) (hx2.trans (by exact_mod_cast hgt.le)),
              haff1 x (le_trans (le_M_right _ _) hx1) hx2]; ring)
          H5 H5' (by rw [hlt']) (by rw [hgt']) ?_
        intro hnb'
        have hM' : M acc0 (c1 + acc1) = ((c1 + acc1).size : ℚ) := M_eq_right hA1'
        have := ih ((c0 :: r0).length + r1.length) (by simp at hn ⊢; omega) (c0 :: r0) r1 acc0
          (c1 + acc1) _ _ rfl h0 hr1
          (fun c hc => by rw [head?_mem hc, add_size]; rw [add_size, add_size] at hgt; omega)
          (fun c hc => by rw [add_size]; have := hr1 c (List.mem_of_mem_head? hc); omega)
          (not_and_of_and_false hnb')
          (by
            intro hb
            rw [hM', seg_advance h1 le_rfl]
            rw [hlt'] at hb
            simp at hb
            exact hb.2)
          (by
            intro hb
            rw [hM', seg_advance h1 le_rfl]
            rw [hgt'] at hb
            simp at hb
            exact hb.2)
        rw [hM', exists_seg_advance_left h1 (seg acc0 (c0 :: r0)) le_rfl,
          exists_seg_advance_right h1 (seg acc0 (c0 :: r0)) le_rfl] at this
        exact this
      · rw [if_neg hgt]
        push Not at hgt
        -- unproc_side = 0: P = c0 + acc0 is compared against the segment [acc1, c1 + acc1]
        have hm : M acc0 acc1 ≤ ((c0 + acc0).size : ℚ) := M_le hB0' hA0'
        have hf0 : seg acc0 (c0 :: r0) ((c0 + acc0).size : ℚ) = (c0 + acc0).fee := seg_at_break hc0
        have hf1 : seg acc1 (c1 :: r1) ((c0 + acc0).size : ℚ) =
            acc1.fee + c1.fee * (((c0 + acc0).size : ℚ) - acc1.size) / c1.size :=
          seg_cons_of_le (by exact_mod_cast hA0') (by exact_mod_cast hgt)
        have hgt' : ((c0 + acc0 - acc1).byRatioCmp c1 == .gt) =
            decide (seg acc1 (c1 :: r1) ((c0 + acc0).size : ℚ) <
              seg acc0 (c0 :: r0) ((c0 + acc0).size : ℚ)) := by
          rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_gt_iff _ _ _ hc1, hf0, hf1]
        have hlt' : ((c0 + acc0 - acc1).byRatioCmp c1 == .lt) =
            decide (seg acc0 (c0 :: r0) ((c0 + acc0).size : ℚ) <
              seg acc1 (c1 :: r1) ((c0 + acc0).size : ℚ)) := by
          rw [Bool.beq_eq_decide_eq, decide_eq_decide, byRatio_sub_lt_iff _ _ _ hc1, hf0, hf1]
        refine step_partial (f0 := seg acc0 (c0 :: r0)) (f1 := seg acc1 (c1 :: r1)) hm
          (α := α0 - α1) (β := β0 - β1)
          (fun x hx1 hx2 => by
            rw [haff0 x (le_trans (le_M_left _ _) hx1) hx2,
              haff1 x (le_trans (le_M_right _ _) hx1) (hx2.trans (by exact_mod_cast hgt))]; ring)
          H5 H5' (by rw [hgt']) (by rw [hlt']) ?_
        intro hnb'
        by_cases heq : (c1 + acc1).size = (c0 + acc0).size
        · rw [if_pos heq]
          -- B.size == P.size: both sides advance
          have hM' : M (c0 + acc0) (c1 + acc1) = ((c0 + acc0).size : ℚ) := M_eq_left heq.le
          have hle1 : ((c1 + acc1).size : ℚ) ≤ ((c0 + acc0).size : ℚ) := by exact_mod_cast heq.le
          have := ih (r0.length + r1.length) (by simp at hn ⊢; omega) r0 r1 (c0 + acc0)
            (c1 + acc1) _ _ rfl hr0 hr1
            (fun c hc => by have := hr0 c (List.mem_of_mem_head? hc); omega)
            (fun c hc => by have := hr1 c (List.mem_of_mem_head? hc); omega)
            (not_and_of_and_false hnb')
            (by
              intro hb
              rw [hM', seg_advance h0 le_rfl, seg_advance h1 hle1]
              rw [hgt'] at hb
              simp at hb
              exact hb.2)
            (by
              intro hb
              rw [hM', seg_advance h0 le_rfl, seg_advance h1 hle1]
              rw [hlt'] at hb
              simp at hb
              exact hb.2)
          rw [hM', exists_seg_advance_left h1 (seg (c0 + acc0) r0) hle1,
            exists_seg_advance_right h0 (seg acc1 (c1 :: r1)) le_rfl,
            exists_seg_advance_left h0 (seg (c1 + acc1) r1) le_rfl,
            exists_seg_advance_right h1 (seg acc0 (c0 :: r0)) hle1] at this
          exact this
        · rw [if_neg heq]
          have hM' : M (c0 + acc0) acc1 = ((c0 + acc0).size : ℚ) := M_eq_left hA0'
          have := ih (r0.length + (c1 :: r1).length) (by simp at hn ⊢; omega) r0 (c1 :: r1)
            (c0 + acc0) acc1 _ _ rfl hr0 h1
            (fun c hc => by rw [add_size]; have := hr0 c (List.mem_of_mem_head? hc); omega)
            (fun c hc => by
              rw [head?_mem hc]
              have e1 := add_size c1 acc1
              omega)
            (not_and_of_and_false hnb')
            (by
              intro hb
              rw [hM', seg_advance h0 le_rfl]
              rw [hgt'] at hb
              simp at hb
              exact hb.2)
            (by
              intro hb
              rw [hM', seg_advance h0 le_rfl]
              rw [hlt'] at hb
              simp at hb
              exact hb.2)
          rw [hM', exists_seg_advance_right h0 (seg acc1 (c1 :: r1)) le_rfl,
            exists_seg_advance_left h0 (seg acc1 (c1 :: r1)) le_rfl] at this
          exact this

private theorem compareChunks_spec {c0 c1 : List FeeFrac} (h0 : SizesPos c0) (h1 : SizesPos c1) :
    Spec (compareChunks c0 c1) (BetterSomewhere c0 c1) (BetterSomewhere c1 c0) := by
  have key := sweep_spec _ c0 c1 0 0 false false rfl h0 h1
    (fun c hc => by
      show (0 : ℤ) < 0 + c.size
      have := h0 c (List.mem_of_mem_head? hc); omega)
    (fun c hc => by
      show (0 : ℤ) < 0 + c.size
      have := h1 c (List.mem_of_mem_head? hc); omega)
    (by simp)
    (fun _ => by rw [M_zero, seg_zero, seg_zero, diagram_zero h0, diagram_zero h1])
    (fun _ => by rw [M_zero, seg_zero, seg_zero, diagram_zero h0, diagram_zero h1])
  rw [M_zero] at key
  simp only [seg_zero] at key
  unfold compareChunks
  refine (Spec_congr ?_ ?_).1 key
  · simp [BetterSomewhere]
  · simp [BetterSomewhere]

private theorem dominates_iff_not {c0 c1 : List FeeFrac} :
    Dominates c0 c1 ↔ ¬ BetterSomewhere c1 c0 := by
  unfold Dominates BetterSomewhere
  constructor
  · rintro h ⟨x, hx, hlt⟩
    exact absurd (h x hx) (not_le.2 hlt)
  · intro h x hx
    exact not_lt.1 fun hlt => h ⟨x, hx, hlt⟩

private theorem chain_slope {a b : FeeFrac} (ha : 0 < a.size) (hb : 0 < b.size)
    (h : b.fee * a.size ≤ a.fee * b.size) : (b.fee : ℚ) / b.size ≤ a.fee / a.size := by
  rw [div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast ha)]
  exact_mod_cast h

private theorem concave_linear (r : ℚ) {s : Set ℚ} (hs : Convex ℚ s) :
    ConcaveOn ℚ s (fun x => r * x) :=
  ⟨hs, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; exact le_of_eq (by ring)⟩

private theorem concave_shift {g : ℚ → ℚ} {S : ℚ} (hg : ConcaveOn ℚ (Set.Iic S) g) (K s : ℚ) :
    ConcaveOn ℚ (Set.Iic (s + S)) (fun x => K + g (x - s)) := by
  refine ⟨convex_Iic _, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : x - s ∈ Set.Iic S := by simp only [Set.mem_Iic] at hx ⊢; linarith
  have hy' : y - s ∈ Set.Iic S := by simp only [Set.mem_Iic] at hy ⊢; linarith
  have h := hg.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : a * x + b * y - s = a * (x - s) + b * (y - s) := by linear_combination s * hab
  have e2 : a * (K + g (x - s)) + b * (K + g (y - s)) = K + (a * g (x - s) + b * g (y - s)) := by
    linear_combination K * hab
  rw [e, e2]
  linarith

private theorem concave_aux (c : FeeFrac) (cs : List FeeFrac) (hpos : SizesPos (c :: cs))
    (hch : FeeratesNonIncreasing (c :: cs)) :
    ConcaveOn ℚ (Set.Iic (diagramSize (c :: cs) : ℚ)) (diagram (c :: cs)) ∧
    ∀ y : ℚ, y ≤ diagramSize (c :: cs) → diagram (c :: cs) y ≤ (c.fee / c.size) * y := by
  induction cs generalizing c with
  | nil =>
    have e : ∀ y : ℚ, y ≤ (diagramSize [c] : ℚ) → diagram [c] y = c.fee / c.size * y := by
      intro y hy
      rw [diagramSize_cons] at hy
      simp only [diagramSize, List.map_nil, List.sum_nil, add_zero] at hy
      rw [diagram_cons_of_le hy]; ring
    refine ⟨?_, fun y hy => (e y hy).le⟩
    exact (concave_linear (c.fee / c.size) (convex_Iic _)).congr fun y hy => (e y hy).symm
  | cons c' cs ih =>
    obtain ⟨hc, hcs⟩ := sizesPos_cons hpos
    obtain ⟨hc', -⟩ := sizesPos_cons hcs
    have hrel : c'.fee * c.size ≤ c.fee * c'.size := (List.isChain_cons_cons.1 hch).1
    have hch' : FeeratesNonIncreasing (c' :: cs) := (List.isChain_cons_cons.1 hch).2
    obtain ⟨ihc, ihb⟩ := ih c' hcs hch'
    have hrr := chain_slope hc hc' hrel
    have hcq : (0 : ℚ) < c.size := by exact_mod_cast hc
    have hcq' : (0 : ℚ) < c'.size := by exact_mod_cast hc'
    have hS0 : (0 : ℚ) ≤ diagramSize (c' :: cs) := by exact_mod_cast diagramSize_nonneg hcs
    have hsz : (diagramSize (c :: c' :: cs) : ℚ) = c.size + diagramSize (c' :: cs) := by
      rw [diagramSize_cons]; push_cast; rfl
    have hfee : (c.fee : ℚ) = c.fee / c.size * c.size := by field_simp
    have hmin : ∀ x : ℚ, x ≤ c.size + diagramSize (c' :: cs) →
        diagram (c :: c' :: cs) x =
          min (c.fee / c.size * x) (c.fee + diagram (c' :: cs) (x - c.size)) := by
      intro x hx
      by_cases hxs : x ≤ c.size
      · rw [diagram_cons_of_le hxs]
        have hlin : diagram (c' :: cs) (x - c.size) = c'.fee / c'.size * (x - c.size) := by
          rw [diagram_cons_of_le (by linarith)]; ring
        rw [min_eq_left]
        · ring
        · rw [hlin]
          have : (c.fee / c.size - c'.fee / c'.size) * (x - c.size) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          nlinarith
      · push Not at hxs
        rw [diagram_cons_of_ge hpos hxs.le, min_eq_right]
        have h1 := ihb (x - c.size) (by linarith)
        have h2 : c'.fee / c'.size * (x - c.size) ≤ c.fee / c.size * (x - c.size) :=
          mul_le_mul_of_nonneg_right hrr (by linarith)
        nlinarith
    constructor
    · rw [hsz]
      have hconc := (concave_linear (c.fee / c.size) (convex_Iic ((c.size : ℚ) + (diagramSize (c' :: cs) : ℚ)))).inf
        (concave_shift ihc (c.fee : ℚ) (c.size : ℚ))
      exact hconc.congr fun x hx => (hmin x hx).symm
    · intro y hy
      rw [hsz] at hy
      rw [hmin y hy]
      exact min_le_left _ _

/-- The total fee need not *strictly* rise: re-chunking the same transactions (one chunk of fee 4
and size 2 becoming chunks `(3, 1)` and `(1, 1)`) strictly improves the diagram at equal total
fee.  This is why `ImprovesFeerateDiagram` is paired with `PaysForRBF`. -/
theorem solution :
    ∃ old new : List FeeFrac, SizesPos old ∧ SizesPos new ∧ FeeratesNonIncreasing old ∧
      FeeratesNonIncreasing new ∧ ImprovesFeerateDiagram old new ∧
      diagramFee old = diagramFee new := by
  refine ⟨[⟨4, 2⟩], [⟨3, 1⟩, ⟨1, 1⟩], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp at hc; subst hc; norm_num
  · intro c hc; simp at hc; rcases hc with rfl | rfl <;> norm_num
  · simp [FeeratesNonIncreasing]
  · simp [FeeratesNonIncreasing]
  · unfold ImprovesFeerateDiagram; decide +kernel
  · simp [diagramFee]
