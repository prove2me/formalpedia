-- Prove2me | solution 1 for CirclePackingConstants.c_n_nine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T19:48:28.916235+00:00
-- url     : https://prove2.me/submissions/4a916247-138b-449d-9c14-590704fcf0fe

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_r_n_eq_of_sharp_unit_square_separation

noncomputable section

open Filter

namespace CirclePackingConstants

private def band (i : Fin 3) (s x : ℝ) : Prop :=
  if i = 0 then 0 ≤ x ∧ x ≤ s
  else if i = 1 then 1 / 2 - s / 2 ≤ x ∧ x ≤ 1 / 2 + s / 2
  else 1 - s ≤ x ∧ x ≤ 1

private def gridBox (s : ℝ) (i j : Fin 3) (p : Point) : Prop :=
  band i s p.1 ∧ band j s p.2

private def bucket (x : ℝ) : Fin 3 :=
  if x ≤ 1 / 3 then 0 else if x ≤ 2 / 3 then 1 else 2

private lemma bucket_mem_band {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    band (bucket x) (1 / 3) x := by
  unfold bucket
  split_ifs with h₀ h₁
  · simp [band]
    constructor
    · exact hx0
    · norm_num at h₀ ⊢
      exact h₀
  · simp [band]
    constructor <;> norm_num at * <;> linarith
  · simp [band]
    constructor <;> norm_num at * <;> linarith

private lemma sq_sub_le_sq_of_interval {x y a s : ℝ}
    (hs : 0 ≤ s) (hx0 : a ≤ x) (hx1 : x ≤ a + s)
    (hy0 : a ≤ y) (hy1 : y ≤ a + s) :
    (x - y) ^ 2 ≤ s ^ 2 := by
  have h₀ : 0 ≤ s - (x - y) := by linarith
  have h₁ : 0 ≤ s + (x - y) := by linarith
  nlinarith only [mul_nonneg h₀ h₁]

private lemma band_sq_sub_le {i : Fin 3} {s x y : ℝ} (hs : 0 ≤ s)
    (hx : band i s x) (hy : band i s y) : (x - y) ^ 2 ≤ s ^ 2 := by
  fin_cases i <;> simp [band] at hx hy
  · apply sq_sub_le_sq_of_interval (a := 0) hs hx.1 <;> linarith [hx.2, hy.1, hy.2]
  · have hx0 : 1 / 2 - s / 2 ≤ x := by linarith [hx.1]
    have hx1 : x ≤ (1 / 2 - s / 2) + s := by linarith [hx.2]
    have hy0 : 1 / 2 - s / 2 ≤ y := by linarith [hy.1]
    have hy1 : y ≤ (1 / 2 - s / 2) + s := by linarith [hy.2]
    exact sq_sub_le_sq_of_interval hs hx0 hx1 hy0 hy1
  · have hx0 : 1 - s ≤ x := by linarith [hx.1]
    have hx1 : x ≤ (1 - s) + s := by linarith [hx.2]
    have hy0 : 1 - s ≤ y := by linarith [hy.1]
    have hy1 : y ≤ (1 - s) + s := by linarith [hy.2]
    exact sq_sub_le_sq_of_interval hs hx0 hx1 hy0 hy1

private def cell (p : Point) : Fin 3 × Fin 3 := (bucket p.1, bucket p.2)

private lemma same_cell_sqDist_lt_quarter {p q : Point}
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
    (hq : 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1)
    (hc : cell p = cell q) : sqDist p q < 1 / 4 := by
  have hcx : bucket p.1 = bucket q.1 := congrArg Prod.fst hc
  have hcy : bucket p.2 = bucket q.2 := congrArg Prod.snd hc
  have hx := band_sq_sub_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (bucket_mem_band hp.1 hp.2.1)
    (hcx ▸ bucket_mem_band hq.1 hq.2.1)
  have hy := band_sq_sub_le (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (bucket_mem_band hp.2.2.1 hp.2.2.2)
    (hcy ▸ bucket_mem_band hq.2.2.1 hq.2.2.2)
  unfold sqDist
  norm_num at hx hy ⊢
  linarith

private lemma adjacent_left_contract {s ax ay bx byy : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 3)
    (ha0 : 0 ≤ ax) (ha1 : ax ≤ s)
    (hb0 : 1 / 2 - s / 2 ≤ bx) (hb1 : bx ≤ 1 / 2 + s / 2)
    (hdy0 : -s ≤ ay - byy) (hdy1 : ay - byy ≤ s)
    (hfar : 1 / 4 < (ax - bx) ^ 2 + (ay - byy) ^ 2) :
    ax ≤ (9 / 10 : ℝ) * s ∧ 1 / 2 - (9 / 20 : ℝ) * s ≤ bx := by
  have hs_aux : 0 ≤ s * (10 - 29 * s) :=
    mul_nonneg hs0 (by linarith)
  constructor
  · by_contra hnot
    have hab0 : 0 ≤ bx - ax := by linarith
    have hab1 : bx - ax < 1 / 2 - 2 / 5 * s := by linarith
    have hsqx : (ax - bx) ^ 2 ≤ (1 / 2 - 2 / 5 * s) ^ 2 := by
      have hpos : 0 ≤ 1 / 2 - 2 / 5 * s := by linarith
      nlinarith only [sq_nonneg (bx - ax), sq_nonneg (1 / 2 - 2 / 5 * s), hab0, hab1, hpos]
    have hsqy : (ay - byy) ^ 2 ≤ s ^ 2 := by
      have h₀ : 0 ≤ s - (ay - byy) := by linarith
      have h₁ : 0 ≤ s + (ay - byy) := by linarith
      nlinarith only [mul_nonneg h₀ h₁]
    nlinarith only [hfar, hsqx, hsqy, hs_aux]
  · by_contra hnot
    have hab0 : 0 ≤ bx - ax := by linarith
    have hab1 : bx - ax < 1 / 2 - 9 / 20 * s := by linarith
    have hsqx : (ax - bx) ^ 2 ≤ (1 / 2 - 9 / 20 * s) ^ 2 := by
      have hpos : 0 ≤ 1 / 2 - 9 / 20 * s := by linarith
      nlinarith only [sq_nonneg (bx - ax), sq_nonneg (1 / 2 - 9 / 20 * s), hab0, hab1, hpos]
    have hsqy : (ay - byy) ^ 2 ≤ s ^ 2 := by
      have h₀ : 0 ≤ s - (ay - byy) := by linarith
      have h₁ : 0 ≤ s + (ay - byy) := by linarith
      nlinarith only [mul_nonneg h₀ h₁]
    have hs_aux' : 0 ≤ s * (180 - 481 * s) :=
      mul_nonneg hs0 (by linarith)
    nlinarith only [hfar, hsqx, hsqy, hs_aux']

private lemma adjacent_right_contract {s ax ay bx byy : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 3)
    (ha0 : 1 / 2 - s / 2 ≤ ax) (ha1 : ax ≤ 1 / 2 + s / 2)
    (hb0 : 1 - s ≤ bx) (hb1 : bx ≤ 1)
    (hdy0 : -s ≤ ay - byy) (hdy1 : ay - byy ≤ s)
    (hfar : 1 / 4 < (ax - bx) ^ 2 + (ay - byy) ^ 2) :
    ax ≤ 1 / 2 + (9 / 20 : ℝ) * s ∧ 1 - (9 / 10 : ℝ) * s ≤ bx := by
  have h := adjacent_left_contract hs0 hs1
    (ax := 1 - bx) (ay := ay) (bx := 1 - ax) (byy := byy)
    (by linarith) (by linarith) (by linarith) (by linarith)
    hdy0 hdy1 (by
      convert hfar using 1 <;> ring)
  constructor <;> linarith [h.1, h.2]

private lemma diff_mem_of_same_band {i : Fin 3} {s x y : ℝ}
    (hx : band i s x) (hy : band i s y) : -s ≤ x - y ∧ x - y ≤ s := by
  fin_cases i <;> simp [band] at hx hy <;> constructor <;> linarith

private lemma three_bands_contract {s x₀ x₁ x₂ : ℝ}
    (h₀ : band 0 s x₀) (h₁ : band 1 s x₁) (h₂ : band 2 s x₂)
    (h₀₁ : x₀ ≤ (9 / 10 : ℝ) * s ∧ 1 / 2 - (9 / 20 : ℝ) * s ≤ x₁)
    (h₁₂ : x₁ ≤ 1 / 2 + (9 / 20 : ℝ) * s ∧
      1 - (9 / 10 : ℝ) * s ≤ x₂) :
    band 0 ((9 / 10 : ℝ) * s) x₀ ∧
      band 1 ((9 / 10 : ℝ) * s) x₁ ∧
      band 2 ((9 / 10 : ℝ) * s) x₂ := by
  simp [band] at h₀ h₁ h₂ ⊢
  constructor
  · exact ⟨h₀.1, h₀₁.1⟩
  constructor
  · constructor <;> linarith [h₀₁.2, h₁₂.1]
  · constructor <;> linarith [h₁₂.2, h₂.2]

private lemma gridBox_contract {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 3)
    (p : Fin 3 → Fin 3 → Point)
    (hbox : ∀ i j, gridBox s i j (p i j))
    (hfar : ∀ i j i' j', (i, j) ≠ (i', j') →
      1 / 4 < sqDist (p i j) (p i' j')) :
    ∀ i j, gridBox ((9 / 10 : ℝ) * s) i j (p i j) := by
  have hh01 (j : Fin 3) := adjacent_left_contract hs0 hs1
    (hbox 0 j).1.1 (hbox 0 j).1.2 (hbox 1 j).1.1 (hbox 1 j).1.2
    (diff_mem_of_same_band (hbox 0 j).2 (hbox 1 j).2).1
    (diff_mem_of_same_band (hbox 0 j).2 (hbox 1 j).2).2
    (by simpa [sqDist] using hfar 0 j 1 j (by simp))
  have hh12 (j : Fin 3) := adjacent_right_contract hs0 hs1
    (hbox 1 j).1.1 (hbox 1 j).1.2 (hbox 2 j).1.1 (hbox 2 j).1.2
    (diff_mem_of_same_band (hbox 1 j).2 (hbox 2 j).2).1
    (diff_mem_of_same_band (hbox 1 j).2 (hbox 2 j).2).2
    (by simpa [sqDist] using hfar 1 j 2 j (by simp))
  have hv01 (i : Fin 3) := adjacent_left_contract hs0 hs1
    (hbox i 0).2.1 (hbox i 0).2.2 (hbox i 1).2.1 (hbox i 1).2.2
    (diff_mem_of_same_band (hbox i 0).1 (hbox i 1).1).1
    (diff_mem_of_same_band (hbox i 0).1 (hbox i 1).1).2
    (by
      have h := hfar i 0 i 1 (by simp)
      simpa [sqDist, add_comm] using h)
  have hv12 (i : Fin 3) := adjacent_right_contract hs0 hs1
    (hbox i 1).2.1 (hbox i 1).2.2 (hbox i 2).2.1 (hbox i 2).2.2
    (diff_mem_of_same_band (hbox i 1).1 (hbox i 2).1).1
    (diff_mem_of_same_band (hbox i 1).1 (hbox i 2).1).2
    (by
      have h := hfar i 1 i 2 (by simp)
      simpa [sqDist, add_comm] using h)
  have hxrow (j : Fin 3) :
      band 0 ((9 / 10 : ℝ) * s) (p 0 j).1 ∧
        band 1 ((9 / 10 : ℝ) * s) (p 1 j).1 ∧
        band 2 ((9 / 10 : ℝ) * s) (p 2 j).1 :=
    three_bands_contract (hbox 0 j).1 (hbox 1 j).1 (hbox 2 j).1 (hh01 j) (hh12 j)
  have hycol (i : Fin 3) :
      band 0 ((9 / 10 : ℝ) * s) (p i 0).2 ∧
        band 1 ((9 / 10 : ℝ) * s) (p i 1).2 ∧
        band 2 ((9 / 10 : ℝ) * s) (p i 2).2 :=
    three_bands_contract (hbox i 0).2 (hbox i 1).2 (hbox i 2).2 (hv01 i) (hv12 i)
  intro i j
  constructor
  · fin_cases i
    · exact (hxrow j).1
    · exact (hxrow j).2.1
    · exact (hxrow j).2.2
  · fin_cases j
    · exact (hycol i).1
    · exact (hycol i).2.1
    · exact (hycol i).2.2

private def shrink (n : ℕ) : ℝ := (9 / 10 : ℝ) ^ n * (1 / 3)

private lemma adjacent_sqDist_le {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 3) {a b : Point}
    (ha : gridBox s 0 0 a) (hb : gridBox s 1 0 b) :
    sqDist a b ≤ (1 / 2 + s / 2) ^ 2 + s ^ 2 := by
  have hax := ha.1
  have hbx := hb.1
  simp [band] at hax hbx
  have hM : 0 ≤ (1 / 2 : ℝ) + s / 2 := by positivity
  have hx0 : -(1 / 2 + s / 2) ≤ a.1 - b.1 := by linarith
  have hx1 : a.1 - b.1 ≤ 1 / 2 + s / 2 := by linarith
  have hx : (a.1 - b.1) ^ 2 ≤ (1 / 2 + s / 2) ^ 2 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1 / 2 + s / 2) - (a.1 - b.1))
      (by linarith : 0 ≤ (1 / 2 + s / 2) + (a.1 - b.1))]
  have hy := band_sq_sub_le hs ha.2 hb.2
  exact add_le_add hx hy

private lemma nine_points_have_close_pair (p : Fin 9 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) :
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (1 / 2 : ℝ) ^ 2 := by
  by_contra hclose
  push_neg at hclose
  have hfar : ∀ i j, i ≠ j → 1 / 4 < sqDist (p i) (p j) := by
    intro i j hij
    have := hclose i j hij
    norm_num at this ⊢
    exact this
  let f : Fin 9 → Fin 3 × Fin 3 := fun i => cell (p i)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hsmall := same_cell_sqDist_lt_quarter (hp i) (hp j) hij
    exact (not_lt_of_ge (le_of_lt (hfar i j hne))) hsmall
  have hfb : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).2
    constructor
    · exact hf
    · decide
  let e : Fin 9 ≃ Fin 3 × Fin 3 := Equiv.ofBijective f hfb
  let q : Fin 3 → Fin 3 → Point := fun i j => p (e.symm (i, j))
  have hcell (i j : Fin 3) : cell (q i j) = (i, j) := by
    change f (e.symm (i, j)) = (i, j)
    exact e.apply_symm_apply (i, j)
  have hbox0 : ∀ i j, gridBox (1 / 3) i j (q i j) := by
    intro i j
    have hc := hcell i j
    change (bucket (q i j).1, bucket (q i j).2) = (i, j) at hc
    have hcx : bucket (q i j).1 = i := congrArg Prod.fst hc
    have hcy : bucket (q i j).2 = j := congrArg Prod.snd hc
    constructor
    · have hx := bucket_mem_band (x := (q i j).1) (hp _).1 (hp _).2.1
      simpa only [hcx] using hx
    · have hy := bucket_mem_band (x := (q i j).2) (hp _).2.2.1 (hp _).2.2.2
      simpa only [hcy] using hy
  have hfarq : ∀ i j i' j', (i, j) ≠ (i', j') →
      1 / 4 < sqDist (q i j) (q i' j') := by
    intro i j i' j' hne
    apply hfar
    intro heq
    apply hne
    exact e.symm.injective heq
  have hboxes : ∀ n i j, gridBox (shrink n) i j (q i j) := by
    intro n
    induction n with
    | zero =>
        simpa [shrink] using hbox0
    | succ n ih =>
        have hs0 : 0 ≤ shrink n := by
          unfold shrink
          positivity
        have hs1 : shrink n ≤ 1 / 3 := by
          have hpow : (9 / 10 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          unfold shrink
          nlinarith
        have hc := gridBox_contract hs0 hs1 q ih hfarq
        simpa only [shrink, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hc
  let a := q 0 0
  let b := q 1 0
  have hab (n : ℕ) :
      sqDist a b ≤ (1 / 2 + shrink n / 2) ^ 2 + (shrink n) ^ 2 := by
    have hs0 : 0 ≤ shrink n := by
      unfold shrink
      positivity
    have hs1 : shrink n ≤ 1 / 3 := by
      have hpow : (9 / 10 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      unfold shrink
      nlinarith
    exact adjacent_sqDist_le hs0 hs1 (hboxes n 0 0) (hboxes n 1 0)
  have hs_tend : Tendsto shrink atTop (nhds 0) := by
    unfold shrink
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num : (9 / 10 : ℝ) < 1)).mul_const (1 / 3) using 1
    norm_num
  have hupper_tend : Tendsto
      (fun n => (1 / 2 + shrink n / 2) ^ 2 + (shrink n) ^ 2)
      atTop (nhds (1 / 4 : ℝ)) := by
    convert (((tendsto_const_nhds.add (hs_tend.div_const 2)).pow 2).add (hs_tend.pow 2)) using 1 <;>
      norm_num
  have hab_le : sqDist a b ≤ (1 / 4 : ℝ) :=
    ge_of_tendsto hupper_tend (Filter.Eventually.of_forall hab)
  have hab_far : (1 / 4 : ℝ) < sqDist a b := by
    exact hfarq 0 0 1 0 (by simp)
  linarith

private def nineGrid (i : Fin 9) : Point :=
  (((i.val % 3 : ℕ) : ℝ) / 2, ((i.val / 3 : ℕ) : ℝ) / 2)

private lemma nine_grid_separation :
    ∃ p : Fin 9 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) ∧
      ∀ i j, i ≠ j → (1 / 2 : ℝ) ^ 2 ≤ sqDist (p i) (p j) := by
  refine ⟨nineGrid, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [nineGrid]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij <;> norm_num [nineGrid, sqDist]

private theorem c_n_nine_proof : c_n 9 = Real.pi / 4 := by
  have hr := r_n_eq_of_sharp_unit_square_separation
    (n := 9) (d := (1 / 2 : ℝ)) (by norm_num) nine_grid_separation
    (by
      intro p hp
      exact nine_points_have_close_pair p hp)
  unfold c_n
  rw [hr]
  ring

end CirclePackingConstants

theorem solution : CirclePackingConstants.c_n 9 = Real.pi / 4 :=
  CirclePackingConstants.c_n_nine_proof
