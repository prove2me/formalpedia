-- Prove2me | solution 1 for DelaunayStretch.lemma_4_4_pencil
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T01:01:30.082387+00:00
-- url     : https://prove2.me/submissions/a076756e-aefd-4820-af7e-97d3415e11a1

import Mathlib
import Definitions.Def_DelaunayStretch_potential
import Definitions.Def_DelaunayStretch_pencilDisk

open DelaunayStretch

set_option linter.unusedVariables false

namespace L44Aux
open Complex

lemma dpos {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) : 0 < dist aG bG :=
  dist_pos.2 (fun h => by rw [h] at ha; linarith)

lemma dsq (aG bG : ℂ) : dist aG bG ^ 2 = (aG.re - bG.re) ^ 2 + (aG.im - bG.im) ^ 2 := by
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- first component of the unit normal -/
noncomputable def n1 (aG bG : ℂ) : ℝ := (aG.im - bG.im) / dist aG bG
/-- second component of the unit normal -/
noncomputable def n2 (aG bG : ℂ) : ℝ := (bG.re - aG.re) / dist aG bG
/-- pencil radius -/
noncomputable def rr (aG bG : ℂ) (X : ℝ) : ℝ := Real.sqrt (X ^ 2 + dist aG bG ^ 2 / 4)

lemma cre (aG bG : ℂ) (X : ℝ) : (pencilDisk aG bG X).center.re =
    (aG.re + bG.re) / 2 + X * n1 aG bG := by
  simp [pencilDisk, segNormal, n1]

lemma cim (aG bG : ℂ) (X : ℝ) : (pencilDisk aG bG X).center.im =
    (aG.im + bG.im) / 2 + X * n2 aG bG := by
  simp [pencilDisk, segNormal, n2]

lemma rad (aG bG : ℂ) (X : ℝ) : (pencilDisk aG bG X).radius = rr aG bG X := rfl

lemma g2eq {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) :
    aG.im - bG.im = dist aG bG * n1 aG bG := by
  have hd := dpos ha hb
  unfold n1; field_simp

lemma g1eq {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) :
    aG.re - bG.re = -(dist aG bG * n2 aG bG) := by
  have hd := dpos ha hb
  unfold n2; field_simp; ring

lemma nsq {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) :
    n1 aG bG ^ 2 + n2 aG bG ^ 2 = 1 := by
  have hd := dpos ha hb
  have := dsq aG bG
  unfold n1 n2
  field_simp
  linarith

lemma n1pos {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) : 0 < n1 aG bG := by
  have hd := dpos ha hb
  unfold n1; apply div_pos <;> linarith

lemma rr_pos {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) : 0 < rr aG bG X := by
  have hd := dpos ha hb
  unfold rr; apply Real.sqrt_pos.2; positivity

lemma rr_sq (aG bG : ℂ) (X : ℝ) : rr aG bG X ^ 2 = X ^ 2 + dist aG bG ^ 2 / 4 := by
  unfold rr; rw [Real.sq_sqrt]; positivity

lemma offset_eq {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    (pencilState aG bG δ X).offset = X := by
  have h := nsq ha hb
  have h1 := cre aG bG X
  have h2 := cim aG bG X
  simp only [GateState.offset, GateState.mid, GateState.normal, pencilState] at *
  simp only [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im, Complex.sub_im,
    h1, h2]
  simp [n1, n2] at *
  linear_combination X * h

lemma phi_cos {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    Real.cos (pencilState aG bG δ X).phiCoord = n1 aG bG := by
  have hd := dpos ha hb
  have hw : (-I) * (aG - bG) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  simp only [GateState.phiCoord, pencilState]
  rw [Complex.cos_arg hw]
  simp [n1, Complex.dist_eq]

lemma phi_sin {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    Real.sin (pencilState aG bG δ X).phiCoord = n2 aG bG := by
  simp only [GateState.phiCoord, pencilState]
  rw [Complex.sin_arg]
  simp [n2, Complex.dist_eq]

lemma dist_center {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (z : ℂ) (X : ℝ) :
    dist z (pencilDisk aG bG X).center ^ 2 =
      (z.re - (aG.re + bG.re) / 2 - X * n1 aG bG) ^ 2 +
      (z.im - (aG.im + bG.im) / 2 - X * n2 aG bG) ^ 2 := by
  rw [dsq, cre, cim]; ring

lemma onA {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    dist aG (pencilDisk aG bG X).center = rr aG bG X := by
  have h := nsq ha hb
  have e1 := g1eq ha hb
  have e2 := g2eq ha hb
  have hsq : dist aG (pencilDisk aG bG X).center ^ 2 = rr aG bG X ^ 2 := by
    rw [dist_center ha hb, rr_sq]
    have : aG.re - (aG.re + bG.re) / 2 = (aG.re - bG.re) / 2 := by ring
    have : aG.im - (aG.im + bG.im) / 2 = (aG.im - bG.im) / 2 := by ring
    rw [show aG.re - (aG.re + bG.re) / 2 - X * n1 aG bG = (aG.re - bG.re) / 2 - X * n1 aG bG by ring,
      show aG.im - (aG.im + bG.im) / 2 - X * n2 aG bG = (aG.im - bG.im) / 2 - X * n2 aG bG by ring,
      e1, e2]
    linear_combination (dist aG bG ^ 2 / 4 + X ^ 2) * h
  have := rr_pos ha hb X
  nlinarith [dist_nonneg (x := aG) (y := (pencilDisk aG bG X).center)]

lemma onB {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    dist bG (pencilDisk aG bG X).center = rr aG bG X := by
  have h := nsq ha hb
  have e1 := g1eq ha hb
  have e2 := g2eq ha hb
  have hsq : dist bG (pencilDisk aG bG X).center ^ 2 = rr aG bG X ^ 2 := by
    rw [dist_center ha hb, rr_sq]
    rw [show bG.re - (aG.re + bG.re) / 2 - X * n1 aG bG = -(aG.re - bG.re) / 2 - X * n1 aG bG by ring,
      show bG.im - (aG.im + bG.im) / 2 - X * n2 aG bG = -(aG.im - bG.im) / 2 - X * n2 aG bG by ring,
      e1, e2]
    linear_combination (dist aG bG ^ 2 / 4 + X ^ 2) * h
  have := rr_pos ha hb X
  nlinarith [dist_nonneg (x := bG) (y := (pencilDisk aG bG X).center)]


lemma part1a {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (O : Disk) :
    (aG ∈ O.boundary ∧ bG ∈ O.boundary) ↔ ∃ X : ℝ, O = pencilDisk aG bG X := by
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨c, r⟩ := O
    simp only [Disk.boundary, Metric.mem_sphere] at hA hB
    have hd := dpos ha hb
    have h := nsq ha hb
    have e1 := g1eq ha hb
    have e2 := g2eq ha hb
    set w1 := c.re - (aG.re + bG.re) / 2 with hw1
    set w2 := c.im - (aG.im + bG.im) / 2 with hw2
    have heq : (aG.re - c.re) ^ 2 + (aG.im - c.im) ^ 2 =
        (bG.re - c.re) ^ 2 + (bG.im - c.im) ^ 2 := by
      rw [← dsq, ← dsq, hA, hB]
    have hT : dist aG bG * (n1 aG bG * w2 - n2 aG bG * w1) = 0 := by
      rw [hw1, hw2]
      linear_combination (-1/2) * heq - w1 * e1 - w2 * e2
    have hk : n1 aG bG * w2 = n2 aG bG * w1 := by
      have := (mul_eq_zero.1 hT).resolve_left hd.ne'
      linarith
    refine ⟨w1 * n1 aG bG + w2 * n2 aG bG, ?_⟩
    have hc : c = (pencilDisk aG bG (w1 * n1 aG bG + w2 * n2 aG bG)).center := by
      apply Complex.ext
      · rw [cre]
        linear_combination (-w1) * h - n2 aG bG * hk
      · rw [cim]
        linear_combination (-w2) * h + n1 aG bG * hk
    have hr : r = (pencilDisk aG bG (w1 * n1 aG bG + w2 * n2 aG bG)).radius := by
      rw [← hA, rad, ← onA ha hb, ← hc]
    rw [hc, hr]
  · rintro ⟨X, rfl⟩
    simp only [Disk.boundary, Metric.mem_sphere]
    exact ⟨onA ha hb X, onB ha hb X⟩

lemma part1b {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X₁ X₂ : ℝ) (hX : X₁ ≠ X₂) :
    (pencilDisk aG bG X₁).boundary ∩ (pencilDisk aG bG X₂).boundary = {aG, bG} := by
  ext z
  simp only [Set.mem_inter_iff, Disk.boundary, Metric.mem_sphere, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hd := dpos ha hb
    have h := nsq ha hb
    have e1 := g1eq ha hb
    have e2 := g2eq ha hb
    have s1 := dist_center ha hb z X₁
    have s2 := dist_center ha hb z X₂
    rw [h1, rad, rr_sq] at s1
    rw [h2, rad, rr_sq] at s2
    obtain ⟨w1, hw1⟩ : ∃ w1 : ℝ, w1 = z.re - (aG.re + bG.re) / 2 := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w2 : ℝ, w2 = z.im - (aG.im + bG.im) / 2 := ⟨_, rfl⟩
    have s1' : X₁ ^ 2 + dist aG bG ^ 2 / 4 = (w1 - X₁ * n1 aG bG) ^ 2 + (w2 - X₁ * n2 aG bG) ^ 2 := by
      rw [s1, hw1, hw2]
    have s2' : X₂ ^ 2 + dist aG bG ^ 2 / 4 = (w1 - X₂ * n1 aG bG) ^ 2 + (w2 - X₂ * n2 aG bG) ^ 2 := by
      rw [s2, hw1, hw2]
    have hp0 : (X₂ - X₁) * (2 * (w1 * n1 aG bG + w2 * n2 aG bG)) = 0 := by
      linear_combination s2' - s1' + (X₂ ^ 2 - X₁ ^ 2) * h
    have hp : w1 * n1 aG bG + w2 * n2 aG bG = 0 := by
      have := (mul_eq_zero.1 hp0).resolve_left (sub_ne_zero.2 hX.symm)
      linarith
    have hw : w1 ^ 2 + w2 ^ 2 = dist aG bG ^ 2 / 4 := by
      linear_combination -s1' - X₁ ^ 2 * h + 2 * X₁ * hp
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = n1 aG bG * w2 - n2 aG bG * w1 := ⟨_, rfl⟩
    have hl2 : l ^ 2 = (dist aG bG / 2) ^ 2 := by
      rw [hl]
      linear_combination (w1 ^ 2 + w2 ^ 2) * h + hw - (w1 * n1 aG bG + w2 * n2 aG bG) * hp
    have hx1 : w1 = - l * n2 aG bG := by
      rw [hl]; linear_combination (-w1) * h + n1 aG bG * hp
    have hx2 : w2 = l * n1 aG bG := by
      rw [hl]; linear_combination (-w2) * h + n2 aG bG * hp
    have hzr : z.re = (aG.re + bG.re) / 2 + w1 := by rw [hw1]; ring
    have hzi : z.im = (aG.im + bG.im) / 2 + w2 := by rw [hw2]; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hl2 with hl' | hl'
    · left
      apply Complex.ext
      · rw [hzr, hx1, hl']; linear_combination (-1/2) * e1
      · rw [hzi, hx2, hl']; linear_combination (-1/2) * e2
    · right
      apply Complex.ext
      · rw [hzr, hx1, hl']; linear_combination (1/2) * e1
      · rw [hzi, hx2, hl']; linear_combination (1/2) * e2
  · rintro (rfl | rfl)
    · exact ⟨onA ha hb X₁, onA ha hb X₂⟩
    · exact ⟨onB ha hb X₁, onB ha hb X₂⟩

lemma part1c {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X₁ X₂ : ℝ) :
    (pencilDisk aG bG X₁).center.re < (pencilDisk aG bG X₂).center.re ↔ X₁ < X₂ := by
  have := n1pos ha hb
  rw [cre, cre]
  constructor <;> intro h <;> nlinarith


/-- `y` coordinate of the pencil center -/
noncomputable def cy (aG bG : ℂ) (X : ℝ) : ℝ := (aG.im + bG.im) / 2 + X * n2 aG bG

lemma rr_hasDerivAt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    HasDerivAt (rr aG bG) (X / rr aG bG X) X := by
  have hd := dpos ha hb
  have h1 : HasDerivAt (fun Y : ℝ => Y ^ 2 + dist aG bG ^ 2 / 4) (2 * X) X := by
    simpa using (hasDerivAt_pow 2 X).add_const (dist aG bG ^ 2 / 4)
  have h2 := h1.sqrt (by positivity)
  have hr := rr_pos ha hb X
  unfold rr at hr ⊢
  refine h2.congr_deriv ?_
  field_simp

lemma rr_contDiff {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (rr aG bG) := by
  have hd := dpos ha hb
  unfold rr
  exact ((contDiff_id.pow 2).add contDiff_const).sqrt (fun x => by positivity)

lemma u_lt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    -1 < X / rr aG bG X ∧ X / rr aG bG X < 1 := by
  have hd := dpos ha hb
  have hr := rr_pos ha hb X
  have hs := rr_sq aG bG X
  constructor
  · rw [lt_div_iff₀ hr]; nlinarith
  · rw [div_lt_one hr]; nlinarith

lemma v_lt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    -1 < cy aG bG X / rr aG bG X ∧ cy aG bG X / rr aG bG X < 1 := by
  have hr := rr_pos ha hb X
  have hA := dsq aG (pencilDisk aG bG X).center
  have hB := dsq bG (pencilDisk aG bG X).center
  rw [onA ha hb, cim] at hA
  rw [onB ha hb, cim] at hB
  have hc : cy aG bG X = (aG.im + bG.im) / 2 + X * n2 aG bG := rfl
  rw [← hc] at hA hB
  constructor
  · rw [lt_div_iff₀ hr]
    nlinarith [sq_nonneg (aG.re - (pencilDisk aG bG X).center.re)]
  · rw [div_lt_one hr]
    nlinarith [sq_nonneg (bG.re - (pencilDisk aG bG X).center.re)]

lemma theta_fun {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ : ℝ) :
    (fun X => (pencilState aG bG δ X).thetaCoord) = fun X => Real.arccos (X / rr aG bG X) := by
  funext X
  simp only [GateState.thetaCoord, offset_eq ha hb]
  rfl

lemma gamma_fun (aG bG : ℂ) (δ : ℝ) :
    (fun X => (pencilState aG bG δ X).gammaCoord) =
      fun X => Real.arcsin (cy aG bG X / rr aG bG X) := by
  funext X
  simp only [GateState.gammaCoord, pencilState, cim, rad, cy]

lemma psi_fun (aG bG : ℂ) (δ : ℝ) :
    (fun X => (pencilState aG bG δ X).psiCoord) =
      fun X => Complex.arg ((-I) * (aG - bG)) + δ / (2 * rr aG bG X) := by
  funext X
  rfl

lemma phi_fun (aG bG : ℂ) (δ : ℝ) :
    (fun X => (pencilState aG bG δ X).phiCoord) = fun _ => Complex.arg ((-I) * (aG - bG)) := by
  funext X
  rfl

lemma u_hasDerivAt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    HasDerivAt (fun Y => Y / rr aG bG Y)
      ((1 * rr aG bG X - X * (X / rr aG bG X)) / rr aG bG X ^ 2) X :=
  (hasDerivAt_id X).div (rr_hasDerivAt ha hb X) (rr_pos ha hb X).ne'

lemma v_hasDerivAt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    HasDerivAt (fun Y => cy aG bG Y / rr aG bG Y)
      ((n2 aG bG * rr aG bG X - cy aG bG X * (X / rr aG bG X)) / rr aG bG X ^ 2) X := by
  have hc : HasDerivAt (cy aG bG) (n2 aG bG) X := by
    unfold cy
    simpa using ((hasDerivAt_id X).mul_const (n2 aG bG)).const_add ((aG.im + bG.im) / 2)
  exact hc.div (rr_hasDerivAt ha hb X) (rr_pos ha hb X).ne'

lemma theta_hasDerivAt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    HasDerivAt (fun Y => Real.arccos (Y / rr aG bG Y))
      (-Real.sin (Real.arccos (X / rr aG bG X)) / rr aG bG X) X := by
  obtain ⟨h1, h2⟩ := u_lt ha hb X
  have h := (Real.hasDerivAt_arccos h1.ne' h2.ne).comp X (u_hasDerivAt ha hb X)
  refine h.congr_deriv ?_
  have hr := rr_pos ha hb X
  rw [Real.sin_arccos]
  have hpos : 0 < 1 - (X / rr aG bG X) ^ 2 := by
    have : (X / rr aG bG X) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    linarith
  have hS := Real.sqrt_pos.2 hpos
  have hS2 := Real.sq_sqrt hpos.le
  set S := Real.sqrt (1 - (X / rr aG bG X) ^ 2)
  field_simp
  field_simp at hS2
  linear_combination hS2

lemma gamma_hasDerivAt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (X : ℝ) :
    HasDerivAt (fun Y => Real.arcsin (cy aG bG Y / rr aG bG Y))
      ((n2 aG bG - Real.sin (Real.arcsin (cy aG bG X / rr aG bG X)) *
          Real.cos (Real.arccos (X / rr aG bG X))) /
        Real.cos (Real.arcsin (cy aG bG X / rr aG bG X)) / rr aG bG X) X := by
  obtain ⟨h1, h2⟩ := v_lt ha hb X
  obtain ⟨k1, k2⟩ := u_lt ha hb X
  have h := (Real.hasDerivAt_arcsin h1.ne' h2.ne).comp X (v_hasDerivAt ha hb X)
  refine h.congr_deriv ?_
  have hr := rr_pos ha hb X
  rw [Real.cos_arcsin, Real.sin_arcsin h1.le h2.le, Real.cos_arccos k1.le k2.le]
  have hpos : 0 < 1 - (cy aG bG X / rr aG bG X) ^ 2 := by
    have : (cy aG bG X / rr aG bG X) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]; exact ⟨h1, h2⟩
    linarith
  have hS := Real.sqrt_pos.2 hpos
  set S := Real.sqrt (1 - (cy aG bG X / rr aG bG X) ^ 2)
  field_simp

lemma psi_hasDerivAt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (c δ X : ℝ) :
    HasDerivAt (fun Y => c + δ / (2 * rr aG bG Y))
      (-(δ / (2 * rr aG bG X)) * (X / rr aG bG X) / rr aG bG X) X := by
  have hr := rr_pos ha hb X
  have h := (hasDerivAt_const X δ).div ((rr_hasDerivAt ha hb X).const_mul 2) (by positivity)
  refine (h.const_add c).congr_deriv ?_
  field_simp
  ring


lemma theta_at {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    (pencilState aG bG δ X).thetaCoord = Real.arccos (X / rr aG bG X) :=
  congrFun (theta_fun ha hb δ) X

lemma gamma_at (aG bG : ℂ) (δ X : ℝ) :
    (pencilState aG bG δ X).gammaCoord = Real.arcsin (cy aG bG X / rr aG bG X) :=
  congrFun (gamma_fun aG bG δ) X

lemma cos_theta {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    Real.cos (pencilState aG bG δ X).thetaCoord = X / rr aG bG X := by
  obtain ⟨k1, k2⟩ := u_lt ha hb X
  rw [theta_at ha hb, Real.cos_arccos k1.le k2.le]

lemma rr_hasDerivAt' {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    HasDerivAt (rr aG bG) (Real.cos (pencilState aG bG δ X).thetaCoord) X := by
  rw [cos_theta ha hb]; exact rr_hasDerivAt ha hb X

lemma theta_hasDerivAt' {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    HasDerivAt (fun Y => (pencilState aG bG δ Y).thetaCoord)
      (-Real.sin (pencilState aG bG δ X).thetaCoord / rr aG bG X) X := by
  rw [theta_fun ha hb, theta_at ha hb]; exact theta_hasDerivAt ha hb X

lemma gamma_hasDerivAt' {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    HasDerivAt (fun Y => (pencilState aG bG δ Y).gammaCoord)
      (pencilA (pencilState aG bG δ X).angularCoords / rr aG bG X) X := by
  have e : pencilA (pencilState aG bG δ X).angularCoords =
      (n2 aG bG - Real.sin (Real.arcsin (cy aG bG X / rr aG bG X)) *
          Real.cos (Real.arccos (X / rr aG bG X))) /
        Real.cos (Real.arcsin (cy aG bG X / rr aG bG X)) := by
    simp only [pencilA, GateState.angularCoords]
    rw [phi_sin ha hb, gamma_at, theta_at ha hb]
  rw [gamma_fun, e]; exact gamma_hasDerivAt ha hb X

lemma psi_hasDerivAt' {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    HasDerivAt (fun Y => (pencilState aG bG δ Y).psiCoord)
      (-((pencilState aG bG δ X).psiCoord - (pencilState aG bG δ X).phiCoord) *
        Real.cos (pencilState aG bG δ X).thetaCoord / rr aG bG X) X := by
  have e : (pencilState aG bG δ X).psiCoord - (pencilState aG bG δ X).phiCoord =
      δ / (2 * rr aG bG X) := by
    show Complex.arg ((-I) * (aG - bG)) + δ / (2 * rr aG bG X) - Complex.arg ((-I) * (aG - bG)) = _
    ring
  rw [psi_fun, e, cos_theta ha hb]
  exact psi_hasDerivAt ha hb _ δ X

lemma z_hasDerivAt {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ X : ℝ) :
    HasDerivAt (fun Y => (pencilState aG bG δ Y).angularCoords)
      (pencilA (pencilState aG bG δ X).angularCoords / rr aG bG X, 0,
        -Real.sin (pencilState aG bG δ X).thetaCoord / rr aG bG X,
        -((pencilState aG bG δ X).psiCoord - (pencilState aG bG δ X).phiCoord) *
          Real.cos (pencilState aG bG δ X).thetaCoord / rr aG bG X) X := by
  have hφ : HasDerivAt (fun Y => (pencilState aG bG δ Y).phiCoord) 0 X := by
    rw [phi_fun]; exact hasDerivAt_const X _
  exact (gamma_hasDerivAt' ha hb δ X).prodMk
    (hφ.prodMk ((theta_hasDerivAt' ha hb δ X).prodMk (psi_hasDerivAt' ha hb δ X)))

lemma cre_hasDerivAt (aG bG : ℂ) (X : ℝ) :
    HasDerivAt (fun Y => (pencilDisk aG bG Y).center.re) (n1 aG bG) X := by
  have : (fun Y => (pencilDisk aG bG Y).center.re) =
      fun Y => (aG.re + bG.re) / 2 + Y * n1 aG bG := funext (cre aG bG)
  rw [this]
  simpa using ((hasDerivAt_id X).mul_const (n1 aG bG)).const_add ((aG.re + bG.re) / 2)

lemma part3 {aG bG : ℂ} (ha : 0 < aG.im) (hb : bG.im < 0) (δ U : ℝ) (H : R4 → ℝ) (X₀ : ℝ)
    (g : R4)
    (hH : HasDerivAt (fun X => H (pencilState aG bG δ X).angularCoords)
      (dot4 g (deriv (fun X => (pencilState aG bG δ X).angularCoords) X₀)) X₀) :
    HasDerivAt (fun X => potential H U (pencilState aG bG δ X))
      (pencilResidual U H g (pencilState aG bG δ X₀).angularCoords) X₀ := by
  have hz := z_hasDerivAt ha hb δ X₀
  rw [hz.deriv] at hH
  have hW := ((rr_hasDerivAt' ha hb δ X₀).mul
    (((theta_hasDerivAt' ha hb δ X₀).const_sub (Real.pi / 2)).sub hH)).add
    (((cre_hasDerivAt aG bG X₀).const_sub (pencilState aG bG δ X₀).crossing.re).const_mul U)
  refine hW.congr_deriv ?_
  have hr := rr_pos ha hb X₀
  rw [← phi_cos ha hb δ X₀]
  simp only [pencilResidual, dot4, GateState.angularCoords, Pi.sub_apply]
  field_simp
  ring

lemma lin4 (L : R4 →L[ℝ] ℝ) (w : R4) :
    L w = dot4 (L (1, 0, 0, 0), L (0, 1, 0, 0), L (0, 0, 1, 0), L (0, 0, 0, 1)) w := by
  obtain ⟨a, b, c, e⟩ := w
  have : ((a, b, c, e) : R4) = a • ((1, 0, 0, 0) : R4) + b • ((0, 1, 0, 0) : R4) +
      c • ((0, 0, 1, 0) : R4) + e • ((0, 0, 0, 1) : R4) := by
    simp
  rw [this, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  simp only [dot4, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk, mul_one]
  ring

end L44Aux

open L44Aux in
theorem solution (aG bG : ℂ) (ha : 0 < aG.im) (hb : bG.im < 0) :
    (∀ O : Disk, (aG ∈ O.boundary ∧ bG ∈ O.boundary) ↔ ∃ X : ℝ, O = pencilDisk aG bG X) ∧
    (∀ X₁ X₂ : ℝ, X₁ ≠ X₂ →
      (pencilDisk aG bG X₁).boundary ∩ (pencilDisk aG bG X₂).boundary = {aG, bG} ∧
        ((pencilDisk aG bG X₁).center.re < (pencilDisk aG bG X₂).center.re ↔ X₁ < X₂)) ∧
    (∀ δ : ℝ, |δ| ≤ dist aG bG →
      (∀ X : ℝ, (pencilState aG bG δ X).IsGateState) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).gammaCoord) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).phiCoord) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).thetaCoord) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X => (pencilState aG bG δ X).psiCoord) ∧
      (∀ X₁ X₂ : ℝ, (pencilState aG bG δ X₁).phiCoord = (pencilState aG bG δ X₂).phiCoord) ∧
      (∀ X : ℝ,
        deriv (fun Y => (pencilDisk aG bG Y).radius) X = Real.cos (pencilState aG bG δ X).thetaCoord ∧
        (pencilDisk aG bG X).radius * deriv (fun Y => (pencilState aG bG δ Y).gammaCoord) X =
          pencilA (pencilState aG bG δ X).angularCoords ∧
        (pencilDisk aG bG X).radius * deriv (fun Y => (pencilState aG bG δ Y).thetaCoord) X =
          -Real.sin (pencilState aG bG δ X).thetaCoord ∧
        (pencilDisk aG bG X).radius * deriv (fun Y => (pencilState aG bG δ Y).psiCoord) X =
          -((pencilState aG bG δ X).psiCoord - (pencilState aG bG δ X).phiCoord) *
            Real.cos (pencilState aG bG δ X).thetaCoord) ∧
      (∀ (U : ℝ) (H : R4 → ℝ) (X₀ : ℝ) (g : R4),
        HasDerivAt (fun X => H (pencilState aG bG δ X).angularCoords)
          (dot4 g (deriv (fun X => (pencilState aG bG δ X).angularCoords) X₀)) X₀ →
        HasDerivAt (fun X => potential H U (pencilState aG bG δ X))
          (pencilResidual U H g (pencilState aG bG δ X₀).angularCoords) X₀) ∧
      (∀ (U : ℝ) (H : R4 → ℝ) (X₀ : ℝ),
        DifferentiableAt ℝ H (pencilState aG bG δ X₀).angularCoords →
        HasDerivAt (fun X => potential H U (pencilState aG bG δ X))
          (pencilResidualGrad U H (pencilState aG bG δ X₀).angularCoords) X₀)) := by
  refine ⟨part1a ha hb, fun X₁ X₂ hX => ⟨part1b ha hb X₁ X₂ hX, part1c ha hb X₁ X₂⟩, ?_⟩
  intro δ hδ
  have hrr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rr aG bG) := rr_contDiff ha hb
  have hrne : ∀ X, rr aG bG X ≠ 0 := fun X => (rr_pos ha hb X).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, ?_, fun U H X₀ g hH => part3 ha hb δ U H X₀ g hH, ?_⟩
  · intro X
    exact ⟨rr_pos ha hb X, Metric.mem_sphere.2 (onA ha hb X), Metric.mem_sphere.2 (onB ha hb X),
      ha, hb, hδ⟩
  · rw [gamma_fun]
    have hcy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cy aG bG) := by unfold cy; fun_prop
    have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => cy aG bG Y / rr aG bG Y) :=
      hcy.div hrr hrne
    refine contDiff_iff_contDiffAt.2 fun X => ?_
    obtain ⟨h1, h2⟩ := v_lt ha hb X
    exact ContDiffAt.comp (g := Real.arcsin) X (Real.contDiffAt_arcsin h1.ne' h2.ne) hv.contDiffAt
  · rw [phi_fun]; exact contDiff_const
  · rw [theta_fun ha hb]
    have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y => Y / rr aG bG Y) :=
      contDiff_id.div hrr hrne
    refine contDiff_iff_contDiffAt.2 fun X => ?_
    obtain ⟨h1, h2⟩ := u_lt ha hb X
    exact ContDiffAt.comp (g := Real.arccos) X (Real.contDiffAt_arccos h1.ne' h2.ne) hu.contDiffAt
  · rw [psi_fun]
    exact contDiff_const.add (contDiff_const.div (contDiff_const.mul hrr)
      (fun X => mul_ne_zero two_ne_zero (hrne X)))
  · intro X
    have hr := rr_pos ha hb X
    refine ⟨(rr_hasDerivAt' ha hb δ X).deriv, ?_, ?_, ?_⟩
    · rw [(gamma_hasDerivAt' ha hb δ X).deriv, rad]; field_simp
    · rw [(theta_hasDerivAt' ha hb δ X).deriv, rad]; field_simp
    · rw [(psi_hasDerivAt' ha hb δ X).deriv, rad]; field_simp
  · intro U H X₀ hd
    have hz := z_hasDerivAt ha hb δ X₀
    have hH := hd.hasFDerivAt.comp_hasDerivAt X₀ hz
    refine part3 ha hb δ U H X₀ _ ?_
    rw [hz.deriv]
    have e := lin4 (fderiv ℝ H (pencilState aG bG δ X₀).angularCoords)
      (pencilA (pencilState aG bG δ X₀).angularCoords / rr aG bG X₀, 0,
        -Real.sin (pencilState aG bG δ X₀).thetaCoord / rr aG bG X₀,
        -((pencilState aG bG δ X₀).psiCoord - (pencilState aG bG δ X₀).phiCoord) *
          Real.cos (pencilState aG bG δ X₀).thetaCoord / rr aG bG X₀)
    rw [e] at hH
    exact hH
