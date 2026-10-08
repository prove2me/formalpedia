-- Prove2me | solution 1 for ConicQuadIPM.Complementarity.lemma_3_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:22:26.974744+00:00
-- url     : https://prove2.me/submissions/09356d9b-2dfb-4eb8-94e0-68efb76ffc73

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting
open Matrix ConicQuadIPM.Complementarity
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
private lemma coordinate {d : ℕ} (v : Fin d → ℝ) (r : ℕ) (hr : r < d) : coord v r = v ⟨r, hr⟩ := by
  unfold coord
  rw [Finset.sum_eq_single ⟨r, hr⟩]
  · simp
  · intro j hj h; simp [show j.val ≠ r by intro he; apply h; exact Fin.ext he]
  · simp

private lemma taction (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) (a : Fin d) :
    (Tmat .rot d *ᵥ v) a =
    if a.val = 0 then (coord v 0 + coord v 1) / Real.sqrt 2
    else if a.val = 1 then (coord v 0 - coord v 1) / Real.sqrt 2 else v a := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  change (∑ j : Fin d, Tmat .rot d a j * v j) = _
  simp only [Tmat]
  by_cases ha : a.val < 2
  · have he : ∀ j : Fin d, (if a.val < 2 ∧ j.val < 2 then (if a.val = 1 ∧ j.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else if a = j then 1 else 0) =
          (if j = z then 1 / Real.sqrt 2 else 0) + (if j = o then (if a.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else 0) := by
        intro j; simp [ha, z, o, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
    simp_rw [he, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [coordinate v 0 (by omega), coordinate v 1 (by omega)]
    dsimp [z, o]
    split_ifs <;> try omega
    all_goals simp [div_eq_mul_inv, mul_add, add_mul, sub_mul, mul_comm, neg_mul, sub_eq_add_neg]
  · rw [Finset.sum_eq_single a]
    · simp [ha, show a.val ≠ 0 by omega, show a.val ≠ 1 by omega]
    · intro j hj hja; simp [ha, Ne.symm hja]
    · simp

private lemma tail_split (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    tailSq v 1 = coord v 1 ^ 2 + tailSq v 2 := by
  rw [coordinate v 1 (by omega)]
  unfold tailSq
  have he : ∀ j : Fin d, (if 1 ≤ j.val then v j ^ 2 else 0) =
      (if j = (⟨1, by omega⟩ : Fin d) then v j ^ 2 else 0) + (if 2 ≤ j.val then v j ^ 2 else 0) := by
    intro j; simp [Fin.ext_iff]; split_ifs <;> simp_all <;> omega
  simp_rw [he, Finset.sum_add_distrib]
  simp

private lemma tail_nonneg {d : ℕ} (v : Fin d → ℝ) (r : ℕ) : 0 ≤ tailSq v r := by
  apply Finset.sum_nonneg
  intro j hj; split_ifs <;> positivity

private lemma tcoords (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    coord (Tmat .rot d *ᵥ v) 0 = (coord v 0 + coord v 1) / Real.sqrt 2 ∧
    coord (Tmat .rot d *ᵥ v) 1 = (coord v 0 - coord v 1) / Real.sqrt 2 ∧
    tailSq (Tmat .rot d *ᵥ v) 2 = tailSq v 2 := by
  constructor
  · rw [coordinate _ 0 (by omega), taction d hd]; simp
  constructor
  · rw [coordinate _ 1 (by omega), taction d hd]; simp
  · unfold tailSq
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : 2 ≤ j.val
    · simp [h, taction d hd, show j.val ≠ 0 by omega, show j.val ≠ 1 by omega]
    · simp [h]

private theorem rot_equiv (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    inQuad v ↔ inRot (Tmat .rot d *ᵥ v) := by
  obtain ⟨h0, h1, ht⟩ := tcoords d hd v
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hn := tail_nonneg v 2
  have hv := tail_split d hd v
  unfold inQuad inRot
  rw [h0, h1, ht]
  constructor
  · rintro ⟨hq, hq0⟩
    have hplus : 0 ≤ coord v 0 + coord v 1 := by nlinarith
    have hminus : 0 ≤ coord v 0 - coord v 1 := by nlinarith
    refine ⟨?_, div_nonneg hplus hp.le, div_nonneg hminus hp.le⟩
    have he : 2 * ((coord v 0 + coord v 1) / Real.sqrt 2) * ((coord v 0 - coord v 1) / Real.sqrt 2) = coord v 0 ^ 2 - coord v 1 ^ 2 := by
      field_simp
      nlinarith [hs]
    rw [he]; linarith
  · rintro ⟨hr, hp0, hp1⟩
    have hplus : 0 ≤ coord v 0 + coord v 1 := by
      simpa [div_nonneg_iff, hp.le, not_le_of_gt hp] using hp0
    have hminus : 0 ≤ coord v 0 - coord v 1 := by
      simpa [div_nonneg_iff, hp.le, not_le_of_gt hp] using hp1
    have he : 2 * ((coord v 0 + coord v 1) / Real.sqrt 2) * ((coord v 0 - coord v 1) / Real.sqrt 2) = coord v 0 ^ 2 - coord v 1 ^ 2 := by
      field_simp
      nlinarith [hs]
    rw [he] at hr
    constructor <;> linarith


private lemma tsq (c : ConeKind) (d : ℕ) (hwf : BlockWF c d) : Tmat c d * Tmat c d = 1 := by
  cases c
  · simp [Tmat]
  · simp [Tmat]
  · have hd := hwf.2.2 rfl
    have hs : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    let z : Fin d := ⟨0, by omega⟩
    let o : Fin d := ⟨1, by omega⟩
    ext a b
    change (∑ j : Fin d, Tmat .rot d a j * Tmat .rot d j b) = if a = b then 1 else 0
    simp only [Tmat]
    by_cases ha : a.val < 2
    · have he : ∀ j : Fin d, (if a.val < 2 ∧ j.val < 2 then (if a.val = 1 ∧ j.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else if a = j then 1 else 0) =
          (if j = z then 1 / Real.sqrt 2 else 0) + (if j = o then (if a.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2) else 0) := by
        intro j; simp [ha, z, o, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
      simp_rw [he, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp [z, o, ha]
      split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
      all_goals
        have hi : (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
          rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
        rw [hi]
        norm_num
    · rw [Finset.sum_eq_single a]
      · simp [ha]
      · intro j hj hja; simp [ha, Ne.symm hja]
      · simp
private lemma qrot_action (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) (a : Fin d) :
    (Qmat .rot d *ᵥ v) a = if a.val = 0 then coord v 1 else if a.val = 1 then coord v 0 else -v a := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  change (∑ j : Fin d, Qmat .rot d a j * v j) = _
  by_cases h0 : a.val = 0
  · rw [Finset.sum_eq_single o]
    · simp [Qmat, h0, z, o, coordinate v 1 (by omega)]
    · intro j hj hjo
      have hn : j.val ≠ 1 := by intro he; apply hjo; exact Fin.ext he
      simp [Qmat, h0, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    · simp
  · by_cases h1 : a.val = 1
    · rw [Finset.sum_eq_single z]
      · simp [Qmat, h1, z, o, coordinate v 0 (by omega)]
      · intro j hj hjz
        have hn : j.val ≠ 0 := by intro he; apply hjz; exact Fin.ext he
        simp [Qmat, h1, hn]; split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      · simp
    · rw [Finset.sum_eq_single a]
      · simp [Qmat, h0, h1, show ¬ a.val < 2 by omega]
      · intro j hj hja
        simp [Qmat, show ¬ a.val < 2 by omega, Ne.symm hja]
      · simp

private lemma quad_form (d : ℕ) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .quad d *ᵥ v) = coord v 0 ^ 2 - tailSq v 1 := by
  have hhead : (∑ j : Fin d, if j.val = 0 then v j ^ 2 else 0) = coord v 0 ^ 2 := by
    cases d with
    | zero => simp [coord]
    | succ d =>
      rw [coordinate v 0 (by omega), Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j hj h; simp [show j.val ≠ 0 by intro he; apply h; exact Fin.ext he]
      · simp
  change (∑ j : Fin d, v j * (Qmat .quad d *ᵥ v) j) = _
  have he : ∀ j : Fin d, v j * (Qmat .quad d *ᵥ v) j =
      (if j.val = 0 then v j ^ 2 else 0) - (if 1 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    simp only [Qmat, Matrix.mulVec_diagonal]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  rw [hhead]; rfl

private lemma rot_form (d : ℕ) (hd : 2 ≤ d) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .rot d *ᵥ v) = 2 * coord v 0 * coord v 1 - tailSq v 2 := by
  have he : ∀ j : Fin d, v j * (Qmat .rot d *ᵥ v) j =
      (if j = (⟨0, by omega⟩ : Fin d) then v j * coord v 1 else 0) +
      (if j = (⟨1, by omega⟩ : Fin d) then v j * coord v 0 else 0) -
      (if 2 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    rw [qrot_action d hd]
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  change (∑ j : Fin d, v j * (Qmat .rot d *ᵥ v) j) = _
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← coordinate v 0 (by omega), ← coordinate v 1 (by omega)]
  unfold tailSq; ring
private lemma tsym (c : ConeKind) (d : ℕ) : (Tmat c d)ᵀ = Tmat c d := by
  cases c
  · simp [Tmat]
  · simp [Tmat]
  · ext a b
    change Tmat .rot d b a = Tmat .rot d a b
    simp only [Tmat]
    simp [and_comm, eq_comm]

private lemma conjugateQ (d : ℕ) (hd : 2 ≤ d) :
    Tmat .rot d * Qmat .rot d * Tmat .rot d = Qmat .quad d := by
  have ht : Tmat .rot d * Tmat .rot d = 1 := tsq .rot d ⟨by simp, by simp, by simpa⟩
  have hc : Tmat .rot d * Qmat .rot d = Qmat .quad d * Tmat .rot d := by
    apply Matrix.ext_iff_mulVec.2
    intro v
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    ext a
    rw [taction d hd]
    have h0 : coord (Qmat .rot d *ᵥ v) 0 = coord v 1 := by
      rw [coordinate _ 0 (by omega), qrot_action d hd]; simp
    have h1 : coord (Qmat .rot d *ᵥ v) 1 = coord v 0 := by
      rw [coordinate _ 1 (by omega), qrot_action d hd]; simp
    rw [h0, h1]
    have hq : ∀ u : Fin d → ℝ, (Qmat .quad d *ᵥ u) a = (if a.val = 0 then 1 else -1) * u a := by
      intro u; simp [Qmat, mulVec_diagonal]
    rw [hq]
    rw [taction d hd, qrot_action d hd]
    split_ifs <;> simp_all <;> ring
  rw [hc, mul_assoc, ht, mul_one]



private lemma lorentz_scalar (a b r t C : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (har : r ≤ a) (hbt : t ≤ b) (hC : C ^ 2 ≤ (r * t) ^ 2) :
    Real.sqrt ((a^2-r^2)*(b^2-t^2)) ≤ a*b+C ∧
    (a*b+C = Real.sqrt ((a^2-r^2)*(b^2-t^2)) →
      a^2*t^2+b^2*r^2+2*a*b*C = 0) := by
  have ha : 0 ≤ a := hr.trans har
  have hb : 0 ≤ b := ht.trans hbt
  have hrt : 0 ≤ r*t := mul_nonneg hr ht
  have hc : -(r*t) ≤ C := by nlinarith
  have hab : r*t ≤ a*b := mul_le_mul har hbt ht ha
  have hx : 0 ≤ a^2-r^2 := by nlinarith
  have hy : 0 ≤ b^2-t^2 := by nlinarith
  have hs : (Real.sqrt ((a^2-r^2)*(b^2-t^2)))^2 = (a^2-r^2)*(b^2-t^2) := Real.sq_sqrt (mul_nonneg hx hy)
  have hs0 := Real.sqrt_nonneg ((a^2-r^2)*(b^2-t^2))
  have hid : (a*b-r*t)^2 - (a^2-r^2)*(b^2-t^2) = (a*t-b*r)^2 := by ring
  have hbound : Real.sqrt ((a^2-r^2)*(b^2-t^2)) ≤ a*b-r*t := by
    nlinarith [sq_nonneg (a*t-b*r)]
  refine ⟨by linarith, ?_⟩
  intro heq
  have hcEq : C = -(r*t) := by linarith
  have hdEq : a*b-r*t = Real.sqrt ((a^2-r^2)*(b^2-t^2)) := by linarith
  have hz : (a*t-b*r)^2 = 0 := by rw [hdEq, hs] at hid; linarith
  rw [hcEq]
  nlinarith [hz]

private lemma quad_bound (d : ℕ) (hd : 1 ≤ d) (x s : Fin d → ℝ)
    (hx : inQuad x) (hs : inQuad s) :
    Real.sqrt ((x ⬝ᵥ (Qmat .quad d *ᵥ x)) * (s ⬝ᵥ (Qmat .quad d *ᵥ s))) ≤ x ⬝ᵥ s ∧
    (x ⬝ᵥ s = Real.sqrt ((x ⬝ᵥ (Qmat .quad d *ᵥ x)) * (s ⬝ᵥ (Qmat .quad d *ᵥ s))) →
      ∀ j : Fin d, j.val ≠ 0 → coord x 0 * s j + coord s 0 * x j = 0) := by
  let u : Fin d → ℝ := fun j => if j.val = 0 then 0 else x j
  let v : Fin d → ℝ := fun j => if j.val = 0 then 0 else s j
  let U := tailSq x 1
  let V := tailSq s 1
  let C := ∑ j : Fin d, u j * v j
  have hu : (∑ j : Fin d, u j ^ 2) = U := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [u, U, tailSq]
    split_ifs <;> simp_all <;> omega
  have hv : (∑ j : Fin d, v j ^ 2) = V := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [v, V, tailSq]
    split_ifs <;> simp_all <;> omega
  have hdot : x ⬝ᵥ s = coord x 0 * coord s 0 + C := by
    have he : ∀ j : Fin d, x j * s j =
        (if j = (⟨0, by omega⟩ : Fin d) then x j * s j else 0) + u j * v j := by
      intro j; simp [u, v, Fin.ext_iff]; split_ifs <;> simp_all
    change (∑ j : Fin d, x j * s j) = _
    rw [show (∑ j : Fin d, x j * s j) =
        ∑ j : Fin d, ((if j = (⟨0, by omega⟩ : Fin d) then x j * s j else 0) + u j * v j) from
        Finset.sum_congr rfl (fun j hj => he j)]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← coordinate x 0 (by omega), ← coordinate s 0 (by omega)]
  have hcs : C^2 ≤ U*V := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    simpa only [hu, hv] using h
  let r := Real.sqrt U
  let t := Real.sqrt V
  have hr : 0 ≤ r := Real.sqrt_nonneg U
  have ht : 0 ≤ t := Real.sqrt_nonneg V
  have hr2 : r^2 = U := Real.sq_sqrt (tail_nonneg x 1)
  have ht2 : t^2 = V := Real.sq_sqrt (tail_nonneg s 1)
  have har : r ≤ coord x 0 := by have := hx.1; have := hx.2; nlinarith
  have hbt : t ≤ coord s 0 := by have := hs.1; have := hs.2; nlinarith
  have hC : C^2 ≤ (r*t)^2 := by rw [mul_pow, hr2, ht2]; exact hcs
  obtain ⟨hb, heq⟩ := lorentz_scalar (coord x 0) (coord s 0) r t C hr ht har hbt hC
  rw [hr2, ht2] at hb heq
  rw [quad_form, quad_form, hdot]
  refine ⟨hb, ?_⟩
  intro he j hj
  have hz := heq he
  have hsum : (∑ l : Fin d, (coord x 0 * v l + coord s 0 * u l)^2) = 0 := by
    have he' : ∀ l : Fin d, (coord x 0 * v l + coord s 0 * u l)^2 =
        coord x 0 ^ 2 * v l ^ 2 + coord s 0 ^ 2 * u l ^ 2 + 2 * coord x 0 * coord s 0 * (u l * v l) := by
      intro l; ring
    simp_rw [he', Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hu, hv]
    exact hz
  have hle : (coord x 0 * v j + coord s 0 * u j)^2 ≤ 0 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun l hl => sq_nonneg (coord x 0 * v l + coord s 0 * u l)) (Finset.mem_univ j)
  have hzj : coord x 0 * v j + coord s 0 * u j = 0 := by nlinarith [sq_nonneg (coord x 0 * v j + coord s 0 * u j)]
  simpa [u, v, hj] using hzj

private lemma arrow_e (d : ℕ) (hd : 1 ≤ d) (v : Fin d → ℝ) :
    arrow v *ᵥ e1 = v := by
  ext a
  change (∑ j : Fin d, arrow v a j * e1 j) = v a
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · by_cases ha : a.val = 0
    · have he : a = (⟨0, by omega⟩ : Fin d) := Fin.ext ha
      rw [he]; simp [arrow, e1]
    · simp [arrow, e1, ha]
  · intro j hj hn
    have hj0 : j.val ≠ 0 := by intro h; apply hn; exact Fin.ext h
    simp [e1, hj0]
  · simp

private lemma arrow_product (d : ℕ) (hd : 1 ≤ d) (x s : Fin d → ℝ)
    (hcancel : ∀ j : Fin d, j.val ≠ 0 → coord x 0 * s j + coord s 0 * x j = 0) :
    (arrow x * arrow s) *ᵥ e1 = (x ⬝ᵥ s) • (e1 : Fin d → ℝ) := by
  rw [← mulVec_mulVec, arrow_e d hd]
  ext a
  by_cases ha : a.val = 0
  · change (∑ j : Fin d, arrow x a j * s j) = (x ⬝ᵥ s) * e1 a
    simp [arrow, ha, e1, dotProduct]
  · have he : ∀ j : Fin d, arrow x a j * s j =
        (if j = (⟨0, by omega⟩ : Fin d) then x a * s j else 0) +
        (if j = a then coord x 0 * s j else 0) := by
      intro j
      by_cases hj0 : j.val = 0
      · have hjz : j = (⟨0, by omega⟩ : Fin d) := Fin.ext hj0
        rw [hjz]
        simp [arrow, ha, Fin.ext_iff, Ne.symm ha]
      · have hjz : j ≠ (⟨0, by omega⟩ : Fin d) := by
          intro h; have := congrArg Fin.val h; exact hj0 this
        by_cases hja : j = a
        · subst j; simp [arrow, ha, hjz]
        · simp [arrow, ha, hj0, hjz, hja, Ne.symm hja]
    change (∑ j : Fin d, arrow x a j * s j) = (x ⬝ᵥ s) * e1 a
    simp_rw [he, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← coordinate s 0 (by omega)]
    simp only [e1, ha, if_false, mul_zero]
    nlinarith [hcancel a ha]

private lemma block_quad {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x : (i : Fin k) → Fin (n i) → ℝ) (hx : inK kind x) :
    ∀ i, inQuad (Tmat (kind i) (n i) *ᵥ x i) := by
  intro i
  have hi := hx i
  have hw := hwf i
  cases hc : kind i
  · have hn : n i = 1 := hw.1 hc
    simp only [hc, inCone, inNonneg] at hi
    simp only [Tmat, one_mulVec]
    constructor
    · have ht : tailSq (x i) 1 = 0 := by
        unfold tailSq
        apply Finset.sum_eq_zero
        intro j hj
        simp [show ¬1 ≤ j.val by have := j.isLt; omega]
      rw [ht]; positivity
    · exact hi
  · simpa [hc, inCone, Tmat] using hi
  · have hd : 2 ≤ n i := hw.2.2 hc
    have hsq := tsq .rot (n i) (by simpa [hc] using hw)
    have he : Tmat .rot (n i) *ᵥ (Tmat .rot (n i) *ᵥ x i) = x i := by
      rw [mulVec_mulVec, hsq, one_mulVec]
    apply (rot_equiv (n i) hd _).2
    rw [he]
    simpa [hc, inCone] using hi

private lemma block_dim (c : ConeKind) (d : ℕ) (hw : BlockWF c d) : 1 ≤ d := by
  cases c
  · have := hw.1 rfl; omega
  · exact hw.2.1 rfl
  · have := hw.2.2 rfl; omega

private lemma block_dot (c : ConeKind) (d : ℕ) (hw : BlockWF c d) (x s : Fin d → ℝ) :
    (Tmat c d *ᵥ x) ⬝ᵥ (Tmat c d *ᵥ s) = x ⬝ᵥ s := by
  rw [dotProduct_mulVec, vecMul_mulVec, tsym, tsq c d hw, vecMul_one]

private lemma block_form (c : ConeKind) (d : ℕ) (hw : BlockWF c d) (x : Fin d → ℝ) :
    (Tmat c d *ᵥ x) ⬝ᵥ (Qmat .quad d *ᵥ (Tmat c d *ᵥ x)) = x ⬝ᵥ (Qmat c d *ᵥ x) := by
  have hcon : Tmat c d * Qmat .quad d * Tmat c d = Qmat c d := by
    cases c
    · have hd := hw.1 rfl
      subst d
      ext a b
      have ha : a.val = 0 := by omega
      have hb : b.val = 0 := by omega
      simp [Tmat, Qmat, diagonal_apply, one_apply, ha, hb, Fin.ext_iff]
    · simp [Tmat]
    · have hd := hw.2.2 rfl
      rw [← conjugateQ d hd]
      have ht := tsq .rot d hw
      calc
        Tmat .rot d * (Tmat .rot d * Qmat .rot d * Tmat .rot d) * Tmat .rot d =
            (Tmat .rot d * Tmat .rot d) * Qmat .rot d * (Tmat .rot d * Tmat .rot d) := by noncomm_ring
        _ = Qmat .rot d := by rw [ht]; simp
  rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec, mulVec_mulVec, tsym, hcon]

theorem solution {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ) (τ κ : ℝ)
    (hN : Nbhd kind n 1 x τ s κ) :
    (∀ i : Fin k,
      (arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1 =
        mu x s τ κ • (e1 : Fin (n i) → ℝ)) ∧
    τ * κ = mu x s τ κ := by
  obtain ⟨hx, hτ, hs, hκ, hNq, hNk⟩ := hN
  simp only [one_mul] at hNq hNk
  have hxb := block_quad kind n hwf x hx
  have hsb := block_quad kind n hwf s hs
  have hbd := fun i => quad_bound (n i) (block_dim (kind i) (n i) (hwf i)) _ _ (hxb i) (hsb i)
  have hlow : ∀ i, mu x s τ κ ≤ x i ⬝ᵥ s i := by
    intro i
    have hb := (hbd i).1
    rw [block_form _ _ (hwf i), block_form _ _ (hwf i), block_dot _ _ (hwf i)] at hb
    exact (hNq i).trans hb
  have htotal : (∑ i, x i ⬝ᵥ s i) + τ*κ = ((k : ℝ)+1) * mu x s τ κ := by
    unfold mu
    field_simp
  have hsum : (∑ i, (x i ⬝ᵥ s i - mu x s τ κ)) + (τ*κ-mu x s τ κ) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [htotal]
  have hnn : 0 ≤ ∑ i, (x i ⬝ᵥ s i - mu x s τ κ) :=
    Finset.sum_nonneg (fun i hi => sub_nonneg.2 (hlow i))
  have htk : τ*κ = mu x s τ κ := by linarith
  have hdot : ∀ i, x i ⬝ᵥ s i = mu x s τ κ := by
    intro i
    have hle : x i ⬝ᵥ s i - mu x s τ κ ≤ ∑ j, (x j ⬝ᵥ s j - mu x s τ κ) :=
      Finset.single_le_sum (fun j hj => sub_nonneg.2 (hlow j)) (Finset.mem_univ i)
    have := hlow i
    linarith
  refine ⟨?_, htk⟩
  intro i
  have hdi : (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) =
      Real.sqrt (((Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Qmat .quad (n i) *ᵥ (Tmat (kind i) (n i) *ᵥ x i))) *
        ((Tmat (kind i) (n i) *ᵥ s i) ⬝ᵥ (Qmat .quad (n i) *ᵥ (Tmat (kind i) (n i) *ᵥ s i)))) := by
    apply le_antisymm
    · rw [block_dot _ _ (hwf i), block_form _ _ (hwf i), block_form _ _ (hwf i), hdot i]
      exact hNq i
    · exact (hbd i).1
  rw [arrow_product _ (block_dim _ _ (hwf i)) _ _ ((hbd i).2 hdi), block_dot _ _ (hwf i), hdot i]

#print axioms solution
