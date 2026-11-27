-- Prove2me | solution 1 for BarelyTestable.LowerBound.square_slack
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:33:31.211718+00:00
-- url     : https://prove2.me/submissions/526e005f-723a-4b3e-8d20-b026dd06e02a

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Construction

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_square_slack

variable {m : ℕ}

/-! ### Coordinates of `insert u S` -/

@[simp] lemma xPart_insert_inl (b : Bool) (S : Cube (Coord m)) :
    xPart (insert (Sum.inl b) S) = xPart S := by
  ext x; simp [xPart]
@[simp] lemma yPart_insert_inl (b : Bool) (S : Cube (Coord m)) :
    yPart (insert (Sum.inl b) S) = yPart S := by
  ext x; simp [yPart]
@[simp] lemma xPart_insert_x (x : Half m) (S : Cube (Coord m)) :
    xPart (insert (Sum.inr (Sum.inl x)) S) = insert x (xPart S) := by
  ext x; simp [xPart]
@[simp] lemma yPart_insert_x (x : Half m) (S : Cube (Coord m)) :
    yPart (insert (Sum.inr (Sum.inl x)) S) = yPart S := by
  ext x; simp [yPart]
@[simp] lemma xPart_insert_y (x : Half m) (S : Cube (Coord m)) :
    xPart (insert (Sum.inr (Sum.inr x)) S) = xPart S := by
  ext x; simp [xPart]
@[simp] lemma yPart_insert_y (x : Half m) (S : Cube (Coord m)) :
    yPart (insert (Sum.inr (Sum.inr x)) S) = insert x (yPart S) := by
  ext x; simp [yPart]
lemma mem_xPart {x : Half m} {S : Cube (Coord m)} : x ∈ xPart S ↔ Sum.inr (Sum.inl x) ∈ S := by
  simp [xPart]
lemma mem_yPart {x : Half m} {S : Cube (Coord m)} : x ∈ yPart S ↔ Sum.inr (Sum.inr x) ∈ S := by
  simp [yPart]

/-! ### Blocks, cardinalities, table values, bit distances -/

lemma block_card_insert {X : HalfSet m} {x : Half m} (hx : x ∉ X) (i : Fin m) :
    (block (insert x X) i).card = (block X i).card + if x.1 = i then 1 else 0 := by
  unfold block
  split_ifs with h
  · have : Finset.univ.filter (fun j => (i, j) ∈ insert x X)
        = insert x.2 (Finset.univ.filter (fun j => (i, j) ∈ X)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      subst h; constructor
      · rintro (h | h)
        · left; rw [← h]
        · right; exact h
      · rintro (h | h)
        · left; rw [h]
        · right; exact h
    rw [this, Finset.card_insert_of_notMem]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; subst h; exact hx
  · rw [add_zero]; congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro (h' | h')
      · exact absurd (congrArg Prod.fst h') (Ne.symm h)
      · exact h'
    · intro h'; exact Or.inr h'

lemma block_card_le (X : HalfSet m) (i : Fin m) : (block X i).card ≤ m := by
  simpa using Finset.card_le_univ (block X i)

lemma card_le_sq (X : HalfSet m) : X.card ≤ m ^ 2 := by
  simpa [sq] using Finset.card_le_univ X

lemma bitDistance_le (v w : Bits m) : bitDistance v w ≤ m := by
  unfold bitDistance; simpa using Finset.card_le_univ (Finset.univ.filter (fun i => v i ≠ w i))

lemma bitDistance_comm (v w : Bits m) : bitDistance v w = bitDistance w v := by
  unfold bitDistance; congr 1; ext i; simp [eq_comm]

lemma theta_nonneg (t : Table m) (z : Address m) : 0 ≤ theta t z := by
  unfold theta; positivity

lemma theta_lt_one (t : Table m) (z : Address m) : theta t z < 1 := by
  unfold theta
  rw [div_lt_one (by positivity)]
  exact_mod_cast (t z).isLt

/-- θ = k / 2^n with k ≤ 2^n - 1. -/
lemma theta_le (t : Table m) (z : Address m) :
    theta t z ≤ 1 - 1 / 2 ^ dimension m := by
  unfold theta
  have h := (t z).isLt
  have hk : ((t z).val : ℝ) + 1 ≤ 2 ^ dimension m := by exact_mod_cast h
  have hp : (0:ℝ) < 2 ^ dimension m := by positivity
  rw [div_le_iff₀ hp, sub_mul, one_div, inv_mul_cancel₀ hp.ne']
  linarith

/-- Bit distance to a parity vector, as a real sum of per-block indicators. -/
lemma bitDistance_parity (X : HalfSet m) (w : Bits m) :
    (bitDistance (parity X) w : ℝ) =
      ∑ i, (if decide ((block X i).card % 2 = 1) ≠ w i then (1:ℝ) else 0) := by
  unfold bitDistance parity
  rw [Finset.card_filter]
  push_cast
  rfl

/-! ### Claim 3.13: one control element changes the base terms by a bounded amount -/

lemma sumsq_step (z z' : Fin m → ℝ) (M : ℝ) (h0 : ∀ i, 0 ≤ z i) (h1 : ∀ i, z i ≤ z' i)
    (h2 : ∀ i, z' i ≤ z i + 1) (hM : ∀ i, z i ≤ M) :
    ∑ i, z i ^ 2 ≤ ∑ i, z' i ^ 2 ∧ ∑ i, z' i ^ 2 ≤ ∑ i, z i ^ 2 + m * (2 * M + 1) := by
  constructor
  · apply Finset.sum_le_sum; intro i _
    nlinarith [h0 i, h1 i]
  · have : ∑ i, z' i ^ 2 ≤ ∑ i : Fin m, (z i ^ 2 + (2 * M + 1)) := by
      apply Finset.sum_le_sum; intro i _
      nlinarith [h0 i, h1 i, h2 i, hM i]
    rw [Finset.sum_add_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this

/-- The constant of Claim 3.13(c). -/
noncomputable def K (m : ℕ) : ℝ := 4 * m * (2 * ((m : ℝ) + m ^ 2) + 1)

lemma baseA_step (X Y X' Y' : HalfSet m)
    (h1 : ∀ i, (block X i).card + Y.card ≤ (block X' i).card + Y'.card)
    (h2 : ∀ i, (block X' i).card + Y'.card ≤ (block X i).card + Y.card + 1) :
    baseA X' Y' ≤ baseA X Y ∧ baseA X Y - K m ≤ baseA X' Y' := by
  have h := sumsq_step (fun i => ((block X i).card : ℝ) + Y.card)
    (fun i => ((block X' i).card : ℝ) + Y'.card) ((m : ℝ) + m ^ 2)
    (fun i => by positivity) (fun i => by exact_mod_cast h1 i) (fun i => by exact_mod_cast h2 i)
    (fun i => by
      have h3 : ((block X i).card : ℝ) ≤ m := by exact_mod_cast block_card_le X i
      have h4 : (Y.card : ℝ) ≤ m ^ 2 := by exact_mod_cast (card_le_sq Y)
      linarith)
  unfold baseA K
  constructor <;> nlinarith [h.1, h.2]

/-- Facts for one step: adding one control element. -/
structure StepFacts (X Y X' Y' : HalfSet m) : Prop where
  card : (X'.card : ℝ) + Y'.card = X.card + Y.card + 1
  a1 : baseA X' Y' ≤ baseA X Y
  a2 : baseA X Y - K m ≤ baseA X' Y'
  b1 : baseB X' Y' ≤ baseB X Y
  b2 : baseB X Y - K m ≤ baseB X' Y'

lemma stepX {X : HalfSet m} {x : Half m} (hx : x ∉ X) (Y : HalfSet m) :
    StepFacts X Y (insert x X) Y := by
  have hA := baseA_step X Y (insert x X) Y
    (fun i => by rw [block_card_insert hx]; omega)
    (fun i => by rw [block_card_insert hx]; split_ifs <;> omega)
  have hB := baseA_step Y X Y (insert x X)
    (fun i => by rw [Finset.card_insert_of_notMem hx]; omega)
    (fun i => by rw [Finset.card_insert_of_notMem hx]; omega)
  exact ⟨by rw [Finset.card_insert_of_notMem hx]; push_cast; ring, hA.1, hA.2, hB.1, hB.2⟩

lemma stepY (X : HalfSet m) {Y : HalfSet m} {y : Half m} (hy : y ∉ Y) :
    StepFacts X Y X (insert y Y) := by
  have hA := baseA_step X Y X (insert y Y)
    (fun i => by rw [Finset.card_insert_of_notMem hy]; omega)
    (fun i => by rw [Finset.card_insert_of_notMem hy]; omega)
  have hB := baseA_step Y X (insert y Y) X
    (fun i => by rw [block_card_insert hy]; omega)
    (fun i => by rw [block_card_insert hy]; split_ifs <;> omega)
  exact ⟨by rw [Finset.card_insert_of_notMem hy]; push_cast; ring, hA.1, hA.2, hB.1, hB.2⟩

lemma poly_bound (hm : 9 ≤ m) : K m + 2 * m + 2 < (m : ℝ) ^ 4 := by
  have h : (9 : ℝ) ≤ m := by exact_mod_cast hm
  unfold K
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ m - 9) (by linarith : (0:ℝ) ≤ m))
    (by linarith : (0:ℝ) ≤ m), mul_nonneg (by linarith : (0:ℝ) ≤ m - 9) (by linarith : (0:ℝ) ≤ m)]

/-- Claims 3.13–3.14: adding one control element strictly decreases every
difference of two slices that differ in one action coordinate. -/
lemma action_step (hm : 9 ≤ m) (r : Sample m) (sign : Bool) {X Y X' Y' : HalfSet m}
    (h : StepFacts X Y X' Y') :
    (∀ b, slice r sign X' Y' true b - slice r sign X' Y' false b
        < slice r sign X Y true b - slice r sign X Y false b) ∧
    (∀ a, slice r sign X' Y' a true - slice r sign X' Y' a false
        < slice r sign X Y a true - slice r sign X Y a false) := by
  have hp := poly_bound hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hK : 0 ≤ K m := by unfold K; positivity
  have ht := fun z => theta_nonneg r.2.2 z
  have ht' := fun z => theta_lt_one r.2.2 z
  have hd := fun (v w : Bits m) => (by exact_mod_cast bitDistance_le v w : (bitDistance v w : ℝ) ≤ m)
  have hd0 := fun (v w : Bits m) => (Nat.cast_nonneg (bitDistance v w) : (0:ℝ) ≤ _)
  have hc := h.card
  have hm4 : (m : ℝ) ^ 4 * ((X'.card : ℝ) + Y'.card) = (m : ℝ) ^ 4 * ((X.card : ℝ) + Y.card) + m ^ 4 := by
    rw [hc]; ring
  constructor
  · intro b; cases b <;> simp only [slice]
    · nlinarith [h.a1, h.a2, h.b1, h.b2]
    · nlinarith [h.a1, h.a2, h.b1, h.b2, ht (alpha r.1 X), ht' (alpha r.1 X'), ht (beta r.2.1 Y'),
        ht' (beta r.2.1 Y), hd (parity X) (r.2.1 Y), hd0 (parity X') (r.2.1 Y'),
        hd (r.1 X) (parity Y), hd0 (r.1 X') (parity Y')]
  · intro a; cases a <;> simp only [slice]
    · nlinarith [ht (beta r.2.1 Y'), ht' (beta r.2.1 Y), ht (beta r.2.1 Y), ht' (beta r.2.1 Y'),
        hd (parity X') (r.2.1 Y'), hd0 (parity X) (r.2.1 Y)]
    · nlinarith [ht (alpha r.1 X), ht' (alpha r.1 X'), hd (r.1 X) (parity Y), hd0 (r.1 X') (parity Y')]


/-! ### Claims 3.11–3.12: squares spanned by two control coordinates -/

/-- Generic shape of a slice, up to swapping the two halves:
`F_A + c·(|X|+|Y|) + K₀ + T(Y) + ε·dist(π(X), w(Y))`. -/
noncomputable def G (c K0 ε : ℝ) (T : HalfSet m → ℝ) (w : HalfSet m → Bits m)
    (X Y : HalfSet m) : ℝ :=
  baseA X Y + c * ((X.card : ℝ) + Y.card) + K0 + T Y + ε * (bitDistance (parity X) (w Y) : ℝ)

/-- Claim 3.11: slack of `F_A` is `8 ∑ sᵢ tᵢ`. -/
lemma baseA_slack {X1 X2 X3 X4 Y1 Y2 Y3 Y4 : HalfSet m} (s t : Fin m → ℝ)
    (h2 : ∀ i, ((block X2 i).card : ℝ) + Y2.card = ((block X1 i).card : ℝ) + Y1.card + s i)
    (h3 : ∀ i, ((block X3 i).card : ℝ) + Y3.card = ((block X1 i).card : ℝ) + Y1.card + t i)
    (h4 : ∀ i, ((block X4 i).card : ℝ) + Y4.card =
      ((block X1 i).card : ℝ) + Y1.card + s i + t i) :
    baseA X2 Y2 + baseA X3 Y3 - baseA X1 Y1 - baseA X4 Y4 = 8 * ∑ i, s i * t i := by
  unfold baseA; simp only [h2, h3, h4]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

lemma card_insert_real {α : Type} [DecidableEq α] {X : Finset α} {x : α} (hx : x ∉ X) :
    ((insert x X).card : ℝ) = X.card + 1 := by
  rw [Finset.card_insert_of_notMem hx]; push_cast; ring

lemma block_card_insert_real {X : HalfSet m} {x : Half m} (hx : x ∉ X) (i : Fin m) :
    ((block (insert x X) i).card : ℝ) = (block X i).card + if x.1 = i then 1 else 0 := by
  rw [block_card_insert hx]; push_cast; rfl

lemma parity_insert_ne {X : HalfSet m} {x : Half m} (hx : x ∉ X) {i : Fin m} (hi : x.1 ≠ i) :
    parity (insert x X) i = parity X i := by
  unfold parity; rw [block_card_insert hx, if_neg hi, add_zero]

/-- Adding one element of `A` changes the distance to a fixed word by at most one. -/
lemma bitDistance_insert {X : HalfSet m} {x : Half m} (hx : x ∉ X) (w : Bits m) :
    (bitDistance (parity (insert x X)) w : ℝ) ≤ bitDistance (parity X) w + 1 ∧
    (bitDistance (parity X) w : ℝ) ≤ bitDistance (parity (insert x X)) w + 1 := by
  unfold bitDistance
  constructor
  · have : Finset.univ.filter (fun i => parity (insert x X) i ≠ w i) ⊆
        insert x.1 (Finset.univ.filter (fun i => parity X i ≠ w i)) := by
      intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      intro h; by_cases hi : x.1 = i
      · exact Or.inl hi.symm
      · right; rwa [parity_insert_ne hx hi] at h
    have := (Finset.card_le_card this).trans (Finset.card_insert_le _ _)
    exact_mod_cast this
  · have : Finset.univ.filter (fun i => parity X i ≠ w i) ⊆
        insert x.1 (Finset.univ.filter (fun i => parity (insert x X) i ≠ w i)) := by
      intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      intro h; by_cases hi : x.1 = i
      · exact Or.inl hi.symm
      · right; rwa [parity_insert_ne hx hi]
    have := (Finset.card_le_card this).trans (Finset.card_insert_le _ _)
    exact_mod_cast this

lemma eps_bound {ε a b : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) (ha : -1 ≤ a ∧ a ≤ 1)
    (hb : -1 ≤ b ∧ b ≤ 1) : -2 ≤ ε * (a - b) := by
  rcases hε with h | h | h <;> subst h <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma ind_bounds (P : Prop) [Decidable P] : 0 ≤ (if P then (1:ℝ) else 0) ∧ (if P then (1:ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

/-- Slack of the generic slice when both elements are added to `A` (Claim 3.12, "both in half A"). -/
lemma G_xx {c K0 ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) (T : HalfSet m → ℝ) (w : HalfSet m → Bits m)
    {X : HalfSet m} {x1 x2 : Half m} (hne : x1 ≠ x2) (h1 : x1 ∉ X) (h2 : x2 ∉ X) (Y : HalfSet m) :
    0 ≤ G c K0 ε T w (insert x1 X) Y + G c K0 ε T w (insert x2 X) Y - G c K0 ε T w X Y
      - G c K0 ε T w (insert x1 (insert x2 X)) Y := by
  have h1' : x1 ∉ insert x2 X := by simp [hne, h1]
  have hb := baseA_slack (X1 := X) (X2 := insert x1 X) (X3 := insert x2 X)
    (X4 := insert x1 (insert x2 X)) (Y1 := Y) (Y2 := Y) (Y3 := Y) (Y4 := Y)
    (fun i => if x1.1 = i then (1:ℝ) else 0) (fun i => if x2.1 = i then (1:ℝ) else 0)
    (fun i => by rw [block_card_insert_real h1]; ring)
    (fun i => by rw [block_card_insert_real h2]; ring)
    (fun i => by rw [block_card_insert_real h1', block_card_insert_real h2]; ring)
  have key : 0 ≤ ∑ i, (8 * ((if x1.1 = i then (1:ℝ) else 0) * (if x2.1 = i then (1:ℝ) else 0)) +
      ε * ((if decide (((block X i).card + if x1.1 = i then 1 else 0) % 2 = 1) ≠ w Y i
              then (1:ℝ) else 0) +
           (if decide (((block X i).card + if x2.1 = i then 1 else 0) % 2 = 1) ≠ w Y i
              then (1:ℝ) else 0) -
           (if decide ((block X i).card % 2 = 1) ≠ w Y i then (1:ℝ) else 0) -
           (if decide (((block X i).card + (if x2.1 = i then 1 else 0) + if x1.1 = i then 1 else 0)
              % 2 = 1) ≠ w Y i then (1:ℝ) else 0))) := by
    apply Finset.sum_nonneg; intro i _
    by_cases e1 : x1.1 = i <;> by_cases e2 : x2.1 = i <;>
      simp only [e1, e2, if_true, if_false, add_zero, mul_zero, mul_one]
    · have := eps_bound hε (a := (if decide (((block X i).card + 1) % 2 = 1) ≠ w Y i
              then (1:ℝ) else 0) - (if decide ((block X i).card % 2 = 1) ≠ w Y i then (1:ℝ) else 0))
        (b := (if decide (((block X i).card + 1 + 1) % 2 = 1) ≠ w Y i then (1:ℝ) else 0) -
          (if decide (((block X i).card + 1) % 2 = 1) ≠ w Y i then (1:ℝ) else 0))
        (by constructor <;> linarith [ind_bounds (decide (((block X i).card + 1) % 2 = 1) ≠ w Y i),
              ind_bounds (decide ((block X i).card % 2 = 1) ≠ w Y i)])
        (by constructor <;> linarith [ind_bounds (decide (((block X i).card + 1) % 2 = 1) ≠ w Y i),
              ind_bounds (decide (((block X i).card + 1 + 1) % 2 = 1) ≠ w Y i)])
      linarith
    · simp
    · simp
    · simp
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at key
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at key
  unfold G
  rw [bitDistance_parity, bitDistance_parity, bitDistance_parity, bitDistance_parity]
  simp only [block_card_insert h1, block_card_insert h2, block_card_insert h1']
  rw [card_insert_real h1, card_insert_real h2, card_insert_real h1', card_insert_real h2]
  linarith

/-- Slack of the generic slice for one element of each half (Claim 3.12, "different halves"). -/
lemma G_xy {c K0 ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) (T : HalfSet m → ℝ) (w : HalfSet m → Bits m)
    {X Y : HalfSet m} {x y : Half m} (hx : x ∉ X) (hy : y ∉ Y) :
    0 ≤ G c K0 ε T w (insert x X) Y + G c K0 ε T w X (insert y Y) - G c K0 ε T w X Y
      - G c K0 ε T w (insert x X) (insert y Y) := by
  have hb := baseA_slack (X1 := X) (X2 := insert x X) (X3 := X) (X4 := insert x X)
    (Y1 := Y) (Y2 := Y) (Y3 := insert y Y) (Y4 := insert y Y)
    (fun i => if x.1 = i then (1:ℝ) else 0) (fun _ => 1)
    (fun i => by rw [block_card_insert_real hx]; ring)
    (fun i => by rw [card_insert_real hy]; ring)
    (fun i => by rw [block_card_insert_real hx, card_insert_real hy]; ring)
  have hs : ∑ i : Fin m, (if x.1 = i then (1:ℝ) else 0) * 1 = 1 := by simp
  rw [hs] at hb
  have d1 := bitDistance_insert hx (w Y)
  have d2 := bitDistance_insert hx (w (insert y Y))
  have := eps_bound hε
    (a := (bitDistance (parity (insert x X)) (w Y) : ℝ) - bitDistance (parity X) (w Y))
    (b := (bitDistance (parity (insert x X)) (w (insert y Y)) : ℝ) -
      bitDistance (parity X) (w (insert y Y)))
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  unfold G
  rw [card_insert_real hx, card_insert_real hy]
  nlinarith

/-- Slack of the generic slice when both elements are added to `B` (Claim 3.12, "both in half B"). -/
lemma G_yy (hm : 1 ≤ m) {c K0 ε : ℝ} (hε : ε = 0 ∨ ε = 1 ∨ ε = -1) (T : HalfSet m → ℝ)
    (hT : ∀ Y, 0 ≤ T Y ∧ T Y < 1) (w : HalfSet m → Bits m)
    {X Y : HalfSet m} {y1 y2 : Half m} (hne : y1 ≠ y2) (h1 : y1 ∉ Y) (h2 : y2 ∉ Y) :
    0 ≤ G c K0 ε T w X (insert y1 Y) + G c K0 ε T w X (insert y2 Y) - G c K0 ε T w X Y
      - G c K0 ε T w X (insert y1 (insert y2 Y)) := by
  have h1' : y1 ∉ insert y2 Y := by simp [hne, h1]
  have hb := baseA_slack (X1 := X) (X2 := X) (X3 := X) (X4 := X)
    (Y1 := Y) (Y2 := insert y1 Y) (Y3 := insert y2 Y) (Y4 := insert y1 (insert y2 Y))
    (fun _ => 1) (fun _ => 1)
    (fun i => by rw [card_insert_real h1]; ring)
    (fun i => by rw [card_insert_real h2]; ring)
    (fun i => by rw [card_insert_real h1', card_insert_real h2]; ring)
  have hs : ∑ _i : Fin m, (1:ℝ) * 1 = m := by simp
  rw [hs] at hb
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hV : ∀ Y', -(m:ℝ) ≤ T Y' + ε * (bitDistance (parity X) (w Y') : ℝ) ∧
      T Y' + ε * (bitDistance (parity X) (w Y') : ℝ) ≤ m + 1 := by
    intro Y'
    have e1 : (bitDistance (parity X) (w Y') : ℝ) ≤ m := by exact_mod_cast bitDistance_le _ _
    have e0 : (0:ℝ) ≤ bitDistance (parity X) (w Y') := Nat.cast_nonneg _
    have := hT Y'
    rcases hε with h | h | h <;> subst h <;> constructor <;> linarith
  have v1 := hV (insert y1 Y); have v2 := hV (insert y2 Y); have v0 := hV Y
  have v12 := hV (insert y1 (insert y2 Y))
  unfold G
  rw [card_insert_real h1, card_insert_real h2, card_insert_real h1', card_insert_real h2]
  linarith [v1.1, v2.1, v0.2, v12.2]

/-! ### The four slices in the generic shape -/

lemma slice_00 (r : Sample m) (sign : Bool) (X Y : HalfSet m) :
    slice r sign X Y false false = G 0 0 0 (fun _ => 0) r.2.1 X Y := by
  simp [slice, G]

lemma slice_01 (r : Sample m) (sign : Bool) (X Y : HalfSet m) :
    slice r sign X Y false true = G (-(m : ℝ) ^ 4) ((if sign then 1 else -1) / 2 ^ dimension m) 1
      (fun Y => theta r.2.2 (beta r.2.1 Y)) r.2.1 X Y := by
  simp only [slice, G]; ring

lemma slice_10 (r : Sample m) (sign : Bool) (X Y : HalfSet m) :
    slice r sign X Y true false = G (-(m : ℝ) ^ 4) 0 0 (fun _ => 0) r.1 Y X := by
  simp only [slice, G, baseB]; ring

lemma slice_11 (r : Sample m) (sign : Bool) (X Y : HalfSet m) :
    slice r sign X Y true true = G (-2 * (m : ℝ) ^ 4) 0 (-1)
      (fun X => theta r.2.2 (alpha r.1 X)) r.1 Y X := by
  simp only [slice, G, baseB]; rw [bitDistance_comm]; ring

lemma thetaB (r : Sample m) : ∀ Y : HalfSet m, 0 ≤ theta r.2.2 (beta r.2.1 Y) ∧
    theta r.2.2 (beta r.2.1 Y) < 1 :=
  fun _ => ⟨theta_nonneg _ _, theta_lt_one _ _⟩

lemma thetaA (r : Sample m) : ∀ X : HalfSet m, 0 ≤ theta r.2.2 (alpha r.1 X) ∧
    theta r.2.2 (alpha r.1 X) < 1 :=
  fun _ => ⟨theta_nonneg _ _, theta_lt_one _ _⟩

lemma zeroT : ∀ _Y : HalfSet m, 0 ≤ (fun _ => (0:ℝ)) _Y ∧ (fun _ => (0:ℝ)) _Y < 1 :=
  fun _ => ⟨le_refl _, one_pos⟩

/-- Claim 3.12: both control elements in `A`. -/
lemma slice_xx (hm : 1 ≤ m) (r : Sample m) (sign a b : Bool) {X : HalfSet m} {x1 x2 : Half m}
    (hne : x1 ≠ x2) (h1 : x1 ∉ X) (h2 : x2 ∉ X) (Y : HalfSet m) :
    0 ≤ slice r sign (insert x1 X) Y a b + slice r sign (insert x2 X) Y a b - slice r sign X Y a b
      - slice r sign (insert x1 (insert x2 X)) Y a b := by
  cases a <;> cases b
  · simp only [slice_00]; exact G_xx (by norm_num) _ _ hne h1 h2 Y
  · simp only [slice_01]; exact G_xx (by norm_num) _ _ hne h1 h2 Y
  · simp only [slice_10]; exact G_yy hm (by norm_num) _ zeroT _ hne h1 h2
  · simp only [slice_11]; exact G_yy hm (by norm_num) _ (thetaA r) _ hne h1 h2

/-- Claim 3.12: both control elements in `B`. -/
lemma slice_yy (hm : 1 ≤ m) (r : Sample m) (sign a b : Bool) {Y : HalfSet m} {y1 y2 : Half m}
    (hne : y1 ≠ y2) (h1 : y1 ∉ Y) (h2 : y2 ∉ Y) (X : HalfSet m) :
    0 ≤ slice r sign X (insert y1 Y) a b + slice r sign X (insert y2 Y) a b - slice r sign X Y a b
      - slice r sign X (insert y1 (insert y2 Y)) a b := by
  cases a <;> cases b
  · simp only [slice_00]; exact G_yy hm (by norm_num) _ zeroT _ hne h1 h2
  · simp only [slice_01]; exact G_yy hm (by norm_num) _ (thetaB r) _ hne h1 h2
  · simp only [slice_10]; exact G_xx (by norm_num) _ _ hne h1 h2 X
  · simp only [slice_11]; exact G_xx (by norm_num) _ _ hne h1 h2 X

/-- Claim 3.12: one control element in each half. -/
lemma slice_xy (r : Sample m) (sign a b : Bool) {X Y : HalfSet m} {x y : Half m}
    (hx : x ∉ X) (hy : y ∉ Y) :
    0 ≤ slice r sign (insert x X) Y a b + slice r sign X (insert y Y) a b - slice r sign X Y a b
      - slice r sign (insert x X) (insert y Y) a b := by
  cases a <;> cases b
  · simp only [slice_00]; exact G_xy (by norm_num) _ _ hx hy
  · simp only [slice_01]; exact G_xy (by norm_num) _ _ hx hy
  · simp only [slice_10]; linarith [G_xy (c := -(m : ℝ) ^ 4) (K0 := 0) (ε := 0) (by norm_num)
      (fun _ => 0) r.1 hy hx]
  · simp only [slice_11]; linarith [G_xy (c := -2 * (m : ℝ) ^ 4) (K0 := 0) (ε := -1) (by norm_num)
      (fun X => theta r.2.2 (alpha r.1 X)) r.1 hy hx]

/-- Claim 3.10: the two action coordinates. -/
lemma slice_actions (r : Sample m) (sign : Bool) (X Y : HalfSet m) :
    slice r sign X Y true false + slice r sign X Y false true - slice r sign X Y false false
      - slice r sign X Y true true =
    (bitDistance (parity X) (r.2.1 Y) : ℝ) + bitDistance (r.1 X) (parity Y) +
      theta r.2.2 (beta r.2.1 Y) - theta r.2.2 (alpha r.1 X) +
      (if sign then 1 else -1) / 2 ^ dimension m := by
  simp only [slice]; ring

lemma actions_center (r : Sample m) (sign : Bool) (X Y : HalfSet m)
    (hc : Center r.1 r.2.1 X Y) :
    slice r sign X Y true false + slice r sign X Y false true - slice r sign X Y false false
      - slice r sign X Y true true = (if sign then 1 else -1) / 2 ^ dimension m := by
  rw [slice_actions]
  have ht : theta r.2.2 (alpha r.1 X) = theta r.2.2 (beta r.2.1 Y) := by rw [hc]
  unfold Center alpha beta at hc
  simp only [Prod.mk.injEq] at hc
  rw [ht, hc.1, ← hc.2]
  simp [bitDistance]

lemma actions_noncenter (r : Sample m) (sign : Bool) (X Y : HalfSet m)
    (hc : ¬ Center r.1 r.2.1 X Y) :
    0 ≤ slice r sign X Y true false + slice r sign X Y false true - slice r sign X Y false false
      - slice r sign X Y true true := by
  rw [slice_actions]
  have hH : 1 ≤ bitDistance (parity X) (r.2.1 Y) + bitDistance (r.1 X) (parity Y) := by
    by_contra h
    have h1 : bitDistance (parity X) (r.2.1 Y) = 0 := by omega
    have h2 : bitDistance (r.1 X) (parity Y) = 0 := by omega
    apply hc
    unfold bitDistance at h1 h2
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1 h2
    unfold Center alpha beta
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => by simpa using h1 (Finset.mem_univ i),
      funext fun i => by simpa using h2 (Finset.mem_univ i)⟩
  have hH' : (1:ℝ) ≤ (bitDistance (parity X) (r.2.1 Y) : ℝ) + bitDistance (r.1 X) (parity Y) := by
    exact_mod_cast hH
  have t1 := theta_nonneg r.2.2 (beta r.2.1 Y)
  have t2 := theta_le r.2.2 (alpha r.1 X)
  have hσ : -(1 / 2 ^ dimension m : ℝ) ≤ (if sign then 1 else -1) / 2 ^ dimension m := by
    have hp : (0:ℝ) < 2 ^ dimension m := by positivity
    cases sign
    · simp [neg_div]
    · simp only [if_true]; rw [one_div]; have := inv_pos.mpr hp; linarith
  linarith

/-! ### Assembly -/

lemma hard_eq (r : Sample m) (sign : Bool) (S : Cube (Coord m)) :
    hard r sign S = slice r sign (xPart S) (yPart S) (decide (Sum.inl false ∈ S))
      (decide (Sum.inl true ∈ S)) := rfl

lemma slack_comm {ι : Type} [DecidableEq ι] (f : Oracle ι) (S : Cube ι) (u v : ι) :
    slack f S u v = slack f S v u := by
  unfold slack; rw [Finset.insert_comm]; ring

/-- Claim 3.14: one action coordinate and one control coordinate. -/
lemma nonneg_mixed (hm : 9 ≤ m) (r : Sample m) (sign : Bool) (S : Cube (Coord m)) (u : Bool)
    (v : Half m ⊕ Half m) (hu : Sum.inl u ∉ S) (hv : Sum.inr v ∉ S) :
    0 ≤ slack (hard r sign) S (Sum.inl u) (Sum.inr v) := by
  rcases v with x | y
  · have hx : x ∉ xPart S := by rwa [mem_xPart]
    have h := action_step hm r sign (stepX hx (yPart S))
    cases u
    · have := h.1 (decide (Sum.inl true ∈ S))
      simp [slack, hard_eq, hu]; linarith
    · have := h.2 (decide (Sum.inl false ∈ S))
      simp [slack, hard_eq, hu]; linarith
  · have hy : y ∉ yPart S := by rwa [mem_yPart]
    have h := action_step hm r sign (stepY (xPart S) hy)
    cases u
    · have := h.1 (decide (Sum.inl true ∈ S))
      simp [slack, hard_eq, hu]; linarith
    · have := h.2 (decide (Sum.inl false ∈ S))
      simp [slack, hard_eq, hu]; linarith

/-- Claim 3.12: two control coordinates. -/
lemma nonneg_ctrl (hm : 9 ≤ m) (r : Sample m) (sign : Bool) (S : Cube (Coord m))
    (u v : Half m ⊕ Half m) (huv : u ≠ v) (hu : Sum.inr u ∉ S) (hv : Sum.inr v ∉ S) :
    0 ≤ slack (hard r sign) S (Sum.inr u) (Sum.inr v) := by
  have hm1 : 1 ≤ m := by omega
  rcases u with x1 | y1 <;> rcases v with x2 | y2
  · have h1 : x1 ∉ xPart S := by rwa [mem_xPart]
    have h2 : x2 ∉ xPart S := by rwa [mem_xPart]
    have hne : x1 ≠ x2 := fun h => huv (by rw [h])
    have := slice_xx hm1 r sign (decide (Sum.inl false ∈ S)) (decide (Sum.inl true ∈ S))
      hne h1 h2 (yPart S)
    simp [slack, hard_eq]; linarith
  · have h1 : x1 ∉ xPart S := by rwa [mem_xPart]
    have h2 : y2 ∉ yPart S := by rwa [mem_yPart]
    have := slice_xy r sign (decide (Sum.inl false ∈ S)) (decide (Sum.inl true ∈ S)) h1 h2
    simp [slack, hard_eq]; linarith
  · have h1 : y1 ∉ yPart S := by rwa [mem_yPart]
    have h2 : x2 ∉ xPart S := by rwa [mem_xPart]
    have := slice_xy r sign (decide (Sum.inl false ∈ S)) (decide (Sum.inl true ∈ S)) h2 h1
    simp [slack, hard_eq]; linarith
  · have h1 : y1 ∉ yPart S := by rwa [mem_yPart]
    have h2 : y2 ∉ yPart S := by rwa [mem_yPart]
    have hne : y1 ≠ y2 := fun h => huv (by rw [h])
    have := slice_yy hm1 r sign (decide (Sum.inl false ∈ S)) (decide (Sum.inl true ∈ S))
      hne h1 h2 (xPart S)
    simp [slack, hard_eq]; linarith

/-- Claim 3.10 for the hard function. -/
lemma slack_actions (r : Sample m) (sign : Bool) (S : Cube (Coord m))
    (hA : Sum.inl false ∉ S) (hB : Sum.inl true ∉ S) :
    slack (hard r sign) S (Sum.inl false) (Sum.inl true) =
      slice r sign (xPart S) (yPart S) true false + slice r sign (xPart S) (yPart S) false true
        - slice r sign (xPart S) (yPart S) false false
        - slice r sign (xPart S) (yPart S) true true := by
  simp [slack, hard_eq, hA, hB]

end BTHelper_square_slack

open BTHelper_square_slack in
theorem solution {m : ℕ} (hm : 9 ≤ m) (r : Sample m) (sign : Bool)
    (S : Cube (Coord m)) (u v : Coord m) (hv : ValidSquare S u v) :
    let special := Center r.1 r.2.1 (xPart S) (yPart S) ∧
      ((u = actionA ∧ v = actionB) ∨ (u = actionB ∧ v = actionA))
    (special → slack (hard r sign) S u v = (if sign then (1 : ℝ) else -1) / 2 ^ dimension m) ∧
    (¬special → 0 ≤ slack (hard r sign) S u v) := by
  intro special
  obtain ⟨huv, hu, hv'⟩ := hv
  rcases u with a1 | c1 <;> rcases v with a2 | c2
  · cases a1 <;> cases a2
    · exact absurd rfl huv
    · rw [slack_actions r sign S hu hv']
      exact ⟨fun hs => actions_center r sign _ _ hs.1,
        fun hs => actions_noncenter r sign _ _ (fun hc => hs ⟨hc, Or.inl ⟨rfl, rfl⟩⟩)⟩
    · rw [slack_comm, slack_actions r sign S hv' hu]
      exact ⟨fun hs => actions_center r sign _ _ hs.1,
        fun hs => actions_noncenter r sign _ _ (fun hc => hs ⟨hc, Or.inr ⟨rfl, rfl⟩⟩)⟩
    · exact absurd rfl huv
  · refine ⟨fun hs => ?_, fun _ => nonneg_mixed hm r sign S a1 c2 hu hv'⟩
    exfalso
    rcases hs.2 with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [actionA, actionB] at h
  · refine ⟨fun hs => ?_, fun _ => ?_⟩
    · exfalso
      rcases hs.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [actionA, actionB] at h
    · rw [slack_comm]; exact nonneg_mixed hm r sign S a2 c1 hv' hu
  · refine ⟨fun hs => ?_, fun _ => nonneg_ctrl hm r sign S c1 c2 (fun h => huv (by rw [h])) hu hv'⟩
    exfalso
    rcases hs.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [actionA, actionB] at h
