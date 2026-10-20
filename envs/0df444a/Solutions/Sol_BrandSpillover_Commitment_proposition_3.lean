-- Prove2me | solution 1 for BrandSpillover.Commitment.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:47:51.663574+00:00
-- url     : https://prove2.me/submissions/e063321e-9a7c-4aa2-b32d-095353296320

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BSHelp
open BrandSpillover.Commitment SupplierAudit.Competition

/-- CM objective under (O,O) with b = a(1-θ). -/
noncomputable def CMoo (θ b u v : ℝ) : ℝ := u*(2-(θ+b)-2*u+v)/3 + v*(2*(θ+b)-1+u-2*v)/3

noncomputable def Qf (d1 d2 : ℝ) : ℝ := (2*d1^2 + 2*d2^2 - 2*d1*d2)/3

lemma Qf_nonneg (d1 d2 : ℝ) : 0 ≤ Qf d1 d2 := by
  unfold Qf; nlinarith [sq_nonneg (d1 - d2), sq_nonneg d1, sq_nonneg d2]

lemma Qf_eq_zero {d1 d2 : ℝ} (h : Qf d1 d2 ≤ 0) : d1 = 0 ∧ d2 = 0 := by
  unfold Qf at h
  have h1 : d1 ^ 2 ≤ 0 := by nlinarith [sq_nonneg (d1 - 2*d2)]
  have h2 : d2 ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2*d1 - d2)]
  exact ⟨by nlinarith [sq_nonneg d1], by nlinarith [sq_nonneg d2]⟩

/-- Regime 1: both participation constraints of Firm S (vs. IO) and Firm W (vs. OI) bind. -/
lemma oo_R1 (θ c b u v : ℝ) (hc : 0 < c) (h3 : θ < 1)
    (hb0 : 0 ≤ b) (hr : c ≤ (2*θ-1-3*b)/2)
    (C2 : ((2-θ-2*c+v)/3)^2 ≤ ((2-(θ+b)-2*u+v)/3)^2)
    (C3 : ((2*θ-1+u-2*c)/3)^2 ≤ ((2*(θ+b)-1+u-2*v)/3)^2) :
    Qf (u - (c - b/2)) (v - (c+b)) / 4 ≤ CMoo θ b (c - b/2) (c+b) - CMoo θ b u v := by
  obtain ⟨d1, rfl⟩ : ∃ d1, u = c - b/2 + d1 := ⟨u - (c - b/2), by ring⟩
  obtain ⟨d2, rfl⟩ : ∃ d2, v = c + b + d2 := ⟨v - (c + b), by ring⟩
  have key : CMoo θ b (c - b/2) (c+b) - CMoo θ b (c-b/2+d1) (c+b+d2) =
      -((2-θ-2*c+3*b)/3)*d1 - ((2*θ-1-2*c-3*b)/3)*d2 + Qf d1 d2 := by
    unfold CMoo Qf; ring
  have e1 : c - b/2 + d1 - (c - b/2) = d1 := by ring
  have e2 : c + b + d2 - (c + b) = d2 := by ring
  rw [key, e1, e2]
  have hg1 : 0 ≤ (2-θ-2*c+3*b)/3 := by linarith
  have hg2 : 0 ≤ (2*θ-1-2*c-3*b)/3 := by linarith
  have P2 : 0 ≤ (-2*d1) * (4 - 2*θ + 2*b - 2*c - 2*d1 + 2*d2) := by
    have : ((2-(θ+b)-2*(c-b/2+d1)+(c+b+d2))/3)^2 - ((2-θ-2*c+(c+b+d2))/3)^2
        = (-2*d1) * (4 - 2*θ + 2*b - 2*c - 2*d1 + 2*d2) / 9 := by ring
    linarith
  have P3 : 0 ≤ (-2*d2) * (4*θ - b - 2 - 2*c + 2*d1 - 2*d2) := by
    have : ((2*(θ+b)-1+(c-b/2+d1)-2*(c+b+d2))/3)^2 - ((2*θ-1+(c-b/2+d1)-2*c)/3)^2
        = (-2*d2) * (4*θ - b - 2 - 2*c + 2*d1 - 2*d2) / 9 := by ring
    linarith
  clear C2 C3 key e1 e2
  unfold Qf
  rcases le_or_gt d1 0 with h1' | h1'
  · rcases le_or_gt d2 0 with h2' | h2'
    · nlinarith [mul_nonneg hg1 (neg_nonneg.mpr h1'), mul_nonneg hg2 (neg_nonneg.mpr h2'),
        sq_nonneg (d1 - d2), sq_nonneg d1, sq_nonneg d2]
    · have hL : 4*θ - b - 2 - 2*c + 2*d1 - 2*d2 ≤ 0 := by
        by_contra hcon; push Not at hcon
        have := mul_pos (by linarith : (0:ℝ) < 2*d2) hcon
        linarith
      have he : 2*((2*θ-1-2*c-3*b)/3) ≤ d2 - d1 := by linarith
      nlinarith [mul_nonneg hg1 (neg_nonneg.mpr h1'), mul_nonneg (sub_nonneg.mpr he) h2'.le,
        sq_nonneg d1]
  · have hL : 4 - 2*θ + 2*b - 2*c - 2*d1 + 2*d2 ≤ 0 := by
      by_contra hcon; push Not at hcon
      have := mul_pos (by linarith : (0:ℝ) < 2*d1) hcon
      linarith
    have he : 2*((2-θ-2*c+3*b)/3) ≤ d1 - d2 := by linarith
    rcases le_or_gt d2 0 with h2' | h2'
    · nlinarith [mul_nonneg hg2 (neg_nonneg.mpr h2'), mul_nonneg (sub_nonneg.mpr he) h1'.le,
        sq_nonneg d2]
    · exfalso
      have hL3 : 4*θ - b - 2 - 2*c + 2*d1 - 2*d2 ≤ 0 := by
        by_contra hcon; push Not at hcon
        have := mul_pos (by linarith : (0:ℝ) < 2*d2) hcon
        linarith
      linarith

/-- Regime 2: only Firm S's constraint (vs. IO) binds. -/
lemma oo_R2 (θ c b u v : ℝ) (hc : 0 < c) (hθ : 0 < θ) (h3 : θ < 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 - θ) (hr : c ≤ (1+b)/2)
    (C2 : ((2-θ-2*c+v)/3)^2 ≤ ((2-(θ+b)-2*u+v)/3)^2) :
    Qf (u - (c - b/2)) (v - (2*c+2*θ-1+b)/4) / 4 ≤
      CMoo θ b (c - b/2) ((2*c+2*θ-1+b)/4) - CMoo θ b u v := by
  obtain ⟨d1, rfl⟩ : ∃ d1, u = c - b/2 + d1 := ⟨u - (c - b/2), by ring⟩
  obtain ⟨d2, rfl⟩ : ∃ d2, v = (2*c+2*θ-1+b)/4 + d2 := ⟨v - (2*c+2*θ-1+b)/4, by ring⟩
  have key : CMoo θ b (c - b/2) ((2*c+2*θ-1+b)/4) - CMoo θ b (c-b/2+d1) ((2*c+2*θ-1+b)/4+d2) =
      -((1-2*c+b)/2)*d1 + Qf d1 d2 := by
    unfold CMoo Qf; ring
  have e1 : c - b/2 + d1 - (c - b/2) = d1 := by ring
  have e2 : (2*c+2*θ-1+b)/4 + d2 - (2*c+2*θ-1+b)/4 = d2 := by ring
  rw [key, e1, e2]
  have hg1 : 0 ≤ (1-2*c+b)/2 := by linarith
  have P2 : 0 ≤ (-2*d1) * (7/2 - θ - 3*c + b/2 - 2*d1 + 2*d2) := by
    have : ((2-(θ+b)-2*(c-b/2+d1)+((2*c+2*θ-1+b)/4+d2))/3)^2
        - ((2-θ-2*c+((2*c+2*θ-1+b)/4+d2))/3)^2
        = (-2*d1) * (7/2 - θ - 3*c + b/2 - 2*d1 + 2*d2) / 9 := by ring
    linarith
  clear C2 key e1 e2
  unfold Qf
  rcases le_or_gt d1 0 with h1' | h1'
  · nlinarith [mul_nonneg hg1 (neg_nonneg.mpr h1'), sq_nonneg (d1 - d2), sq_nonneg d1, sq_nonneg d2]
  · have hL : 7/2 - θ - 3*c + b/2 - 2*d1 + 2*d2 ≤ 0 := by
      by_contra hcon; push Not at hcon
      have := mul_pos (by linarith : (0:ℝ) < 2*d1) hcon
      linarith
    have he : 2*((1-2*c+b)/2) ≤ d1 - d2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr he) h1'.le, sq_nonneg d2]

/-- Regime 3: the unconstrained maximizer. -/
lemma oo_R3 (θ b u v : ℝ) :
    Qf (u - 1/2) (v - (θ+b)/2) / 4 ≤ CMoo θ b (1/2) ((θ+b)/2) - CMoo θ b u v := by
  have key : CMoo θ b (1/2) ((θ+b)/2) - CMoo θ b u v = Qf (u - 1/2) (v - (θ+b)/2) := by
    unfold CMoo Qf; ring
  rw [key]; linarith [Qf_nonneg (u - 1/2) (v - (θ+b)/2)]

/-! Structure-level formulas. -/

lemma profitS_sq (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) :
    profitS P a s w = (quantS P a s w)^2 := by
  unfold profitS quantS quantW cournotPayoff focQS focQW; ring

lemma profitW_sq (P : Params) (a : ℝ) (s : Structure) (w : ℝ × ℝ) :
    profitW P a s w = (quantW P a s w)^2 := by
  unfold profitW quantS quantW cournotPayoff focQS focQW; ring

section
variable (P : Params) (a : ℝ) (w : ℝ × ℝ)
lemma qS_OO : quantS P a .OO w = (2 - (P.θ + a*(1-P.θ)) - 2*w.1 + w.2)/3 := by
  simp [quantS, focQS, brandW, costS, costW, Structure.sOut, Structure.wOut]
lemma qW_OO : quantW P a .OO w = (2*(P.θ + a*(1-P.θ)) - 1 + w.1 - 2*w.2)/3 := by
  simp [quantW, focQW, brandW, costS, costW, Structure.sOut, Structure.wOut]
lemma qS_OI : quantS P a .OI w = (2 - P.θ - 2*w.1 + P.c)/3 := by
  simp [quantS, focQS, brandW, costS, costW, Structure.sOut, Structure.wOut]
lemma qW_OI : quantW P a .OI w = (2*P.θ - 1 + w.1 - 2*P.c)/3 := by
  simp [quantW, focQW, brandW, costS, costW, Structure.sOut, Structure.wOut]
lemma qS_IO : quantS P a .IO w = (2 - P.θ - 2*P.c + w.2)/3 := by
  simp [quantS, focQS, brandW, costS, costW, Structure.sOut, Structure.wOut]
lemma qW_IO : quantW P a .IO w = (2*P.θ - 1 + P.c - 2*w.2)/3 := by
  simp [quantW, focQW, brandW, costS, costW, Structure.sOut, Structure.wOut]
lemma qS_II : quantS P a .II w = (2 - P.θ - P.c)/3 := by
  simp [quantS, focQS, brandW, costS, costW, Structure.sOut, Structure.wOut]; ring
lemma qW_II : quantW P a .II w = (2*P.θ - 1 - P.c)/3 := by
  simp [quantW, focQW, brandW, costS, costW, Structure.sOut, Structure.wOut]; ring

lemma cm_OO : cmProfit P a .OO w = CMoo P.θ (a*(1-P.θ)) w.1 w.2 := by
  simp only [cmProfit, Structure.sOut, Structure.wOut, if_true, qS_OO, qW_OO, CMoo]; ring
lemma cm_OI : cmProfit P a .OI w = w.1 * (2 - P.θ - 2*w.1 + P.c)/3 := by
  simp only [cmProfit, Structure.sOut, Structure.wOut, if_true, qS_OI]; simp; ring
lemma cm_IO : cmProfit P a .IO w = w.2 * (2*P.θ - 1 + P.c - 2*w.2)/3 := by
  simp only [cmProfit, Structure.sOut, Structure.wOut, if_true, qW_IO]; simp; ring
lemma cm_II : cmProfit P a .II w = 0 := by
  simp [cmProfit, Structure.sOut, Structure.wOut]

lemma feas_OO : Feasible P a .OO w ↔
    ((2 - P.θ - P.c)/3)^2 ≤ ((2 - P.θ - 2*w.1 + P.c)/3)^2 ∧
    ((2 - P.θ - 2*P.c + w.2)/3)^2 ≤ ((2 - (P.θ + a*(1-P.θ)) - 2*w.1 + w.2)/3)^2 ∧
    ((2*P.θ - 1 + w.1 - 2*P.c)/3)^2 ≤ ((2*(P.θ + a*(1-P.θ)) - 1 + w.1 - 2*w.2)/3)^2 := by
  simp only [Feasible, profitS_sq, profitW_sq, qS_OO, qW_OO, qS_OI, qW_OI, qS_IO, qS_II]
lemma feas_OI : Feasible P a .OI w ↔
    ((2 - P.θ - P.c)/3)^2 ≤ ((2 - P.θ - 2*w.1 + P.c)/3)^2 := by
  simp only [Feasible, profitS_sq, qS_OI, qS_II]
lemma feas_IO : Feasible P a .IO w ↔
    ((2*P.θ - 1 - P.c)/3)^2 ≤ ((2*P.θ - 1 + P.c - 2*w.2)/3)^2 := by
  simp only [Feasible, profitW_sq, qW_IO, qW_II]
end

/-! The (O,O) program. -/

noncomputable def usOO (P : Params) (a : ℝ) : ℝ := min (P.c - 1 / 2 * a * (1 - P.θ)) (1 / 2)
noncomputable def vsOO (P : Params) (a : ℝ) : ℝ :=
  if P.c ≤ cOO2 P a then
    min (P.c + a * (1 - P.θ)) ((2 * P.c + 2 * P.θ - 1 + a * (1 - P.θ)) / 4)
  else (P.θ + a * (1 - P.θ)) / 2

lemma standing_facts {P : Params} (hP : P.Standing) :
    0 < P.c ∧ (2 + 7*P.c)/7 ≤ P.θ ∧ (1 + P.c)/2 ≤ P.θ ∧ P.θ < 1 := by
  obtain ⟨hc, hθl, hθ1, -, -⟩ := hP
  exact ⟨hc, le_trans (le_max_left _ _) hθl, le_trans (le_max_right _ _) hθl, hθ1⟩

lemma oo_main (P : Params) (hP : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Feasible P a .OO (usOO P a, vsOO P a) ∧
    ∀ w : ℝ × ℝ, Feasible P a .OO w →
      Qf (w.1 - usOO P a) (w.2 - vsOO P a) / 4 ≤
        cmProfit P a .OO (usOO P a, vsOO P a) - cmProfit P a .OO w := by
  obtain ⟨hc, h1, h2, h3⟩ := standing_facts hP
  have hb0 : 0 ≤ a*(1-P.θ) := mul_nonneg ha0 (by linarith)
  have hb1 : a*(1-P.θ) ≤ 1 - P.θ := by nlinarith
  have hhalf : 1/2*a*(1-P.θ) = a*(1-P.θ)/2 := by ring
  unfold usOO vsOO cOO2
  rw [hhalf]
  simp only [feas_OO, cm_OO]
  generalize a*(1-P.θ) = b at *
  have hθ : 0 < P.θ := by linarith
  rcases le_or_gt P.c ((2*P.θ-1-3*b)/2) with hr | hr
  · rw [min_eq_left (by linarith), if_pos (by linarith), min_eq_left (by linarith)]
    refine ⟨⟨sq_le_sq' (by linarith) (by linarith), le_of_eq (by ring), le_of_eq (by ring)⟩, ?_⟩
    rintro w ⟨-, C2, C3⟩
    exact oo_R1 P.θ P.c b w.1 w.2 hc h3 hb0 hr C2 C3
  rcases le_or_gt P.c ((1+b)/2) with hr2 | hr2
  · rw [min_eq_left (by linarith), if_pos hr2, min_eq_right (by linarith)]
    refine ⟨⟨sq_le_sq' (by linarith) (by linarith), le_of_eq (by ring),
      sq_le_sq' (by linarith) (by linarith)⟩, ?_⟩
    rintro w ⟨-, C2, -⟩
    exact oo_R2 P.θ P.c b w.1 w.2 hc hθ h3 hb0 hb1 hr2 C2
  · rw [min_eq_right (by linarith), if_neg (by linarith)]
    refine ⟨⟨sq_le_sq' (by linarith) (by linarith), sq_le_sq' (by linarith) (by linarith),
      sq_le_sq' (by linarith) (by linarith)⟩, ?_⟩
    rintro w -
    exact oo_R3 P.θ b w.1 w.2

lemma oo_opt_iff (P : Params) (hP : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (w : ℝ × ℝ) : IsOptPrices P a .OO w ↔ (w.1 = usOO P a ∧ w.2 = vsOO P a) := by
  obtain ⟨hF, hQ⟩ := oo_main P hP a ha0 ha1
  constructor
  · rintro ⟨hw, hopt⟩
    have h1 := hopt _ hF
    have h2 := hQ w hw
    have := Qf_eq_zero (d1 := w.1 - usOO P a) (d2 := w.2 - vsOO P a) (by linarith)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · rintro ⟨e1, e2⟩
    have hw : w = (usOO P a, vsOO P a) := Prod.ext e1 e2
    subst hw
    refine ⟨hF, fun w' hw' => ?_⟩
    have := hQ w' hw'
    linarith [Qf_nonneg (w'.1 - usOO P a) (w'.2 - vsOO P a)]

/-! The (O,I) program. -/

noncomputable def fOI (θ c u : ℝ) : ℝ := u * (2 - θ - 2*u + c)/3

noncomputable def usOI (P : Params) : ℝ := min P.c ((2 - P.θ + P.c) / 4)

lemma oi_core (P : Params) (hP : P.Standing) :
    ((2 - P.θ - P.c)/3)^2 ≤ ((2 - P.θ - 2*usOI P + P.c)/3)^2 ∧
    0 < fOI P.θ P.c (usOI P) ∧
    ∀ u : ℝ, ((2 - P.θ - P.c)/3)^2 ≤ ((2 - P.θ - 2*u + P.c)/3)^2 →
      fOI P.θ P.c u ≤ fOI P.θ P.c (usOI P) ∧
      (fOI P.θ P.c (usOI P) ≤ fOI P.θ P.c u → u = usOI P) := by
  obtain ⟨hc, h1, h2, h3⟩ := standing_facts hP
  unfold usOI fOI
  rcases le_total P.c ((2 - P.θ + P.c) / 4) with hr | hr
  · rw [min_eq_left hr]
    refine ⟨le_of_eq (by ring), by nlinarith, fun u hu => ?_⟩
    obtain ⟨d, rfl⟩ : ∃ d, u = P.c + d := ⟨u - P.c, by ring⟩
    have key : P.c * (2 - P.θ - 2*P.c + P.c)/3 - (P.c + d) * (2 - P.θ - 2*(P.c+d) + P.c)/3
        = -((2 - P.θ - 3*P.c)/3) * d + 2*d^2/3 := by ring
    have hP2 : 0 ≤ (-2*d) * (2*(2 - P.θ - P.c) - 2*d) := by
      have : ((2 - P.θ - 2*(P.c+d) + P.c)/3)^2 - ((2 - P.θ - P.c)/3)^2
          = (-2*d) * (2*(2 - P.θ - P.c) - 2*d) / 9 := by ring
      linarith
    have hg : 0 ≤ (2 - P.θ - 3*P.c)/3 := by linarith
    rcases le_or_gt d 0 with hd | hd
    · constructor
      · nlinarith [mul_nonneg hg (neg_nonneg.mpr hd), sq_nonneg d]
      · intro hle
        have : d^2 ≤ 0 := by nlinarith [mul_nonneg hg (neg_nonneg.mpr hd), sq_nonneg d]
        have : d = 0 := by nlinarith [sq_nonneg d]
        subst this; ring
    · have hL : 2*(2 - P.θ - P.c) - 2*d ≤ 0 := by
        by_contra hcon; push Not at hcon
        have := mul_pos (by linarith : (0:ℝ) < 2*d) hcon
        linarith
      have hpos : 0 < d * ((2 - P.θ + P.c)/3) := mul_pos hd (by linarith)
      have : -((2 - P.θ - 3*P.c)/3) * d + 2*d^2/3 ≥ d * ((2 - P.θ + P.c)/3) := by
        nlinarith [mul_nonneg hd.le (by linarith : (0:ℝ) ≤ d - (2 - P.θ - P.c))]
      constructor
      · linarith
      · intro hle; exfalso; linarith
  · rw [min_eq_right hr]
    refine ⟨sq_le_sq' (by linarith) (by linarith), by nlinarith, fun u _ => ?_⟩
    have key : (2 - P.θ + P.c) / 4 * (2 - P.θ - 2*((2 - P.θ + P.c) / 4) + P.c)/3
        - u * (2 - P.θ - 2*u + P.c)/3 = 2*(u - (2 - P.θ + P.c) / 4)^2/3 := by ring
    constructor
    · nlinarith [sq_nonneg (u - (2 - P.θ + P.c) / 4)]
    · intro hle
      have : (u - (2 - P.θ + P.c) / 4)^2 ≤ 0 := by linarith
      have : u - (2 - P.θ + P.c) / 4 = 0 := by nlinarith [sq_nonneg (u - (2 - P.θ + P.c) / 4)]
      linarith

lemma oi_opt_iff (P : Params) (hP : P.Standing) (a : ℝ) (w : ℝ × ℝ) :
    IsOptPrices P a .OI w ↔ w.1 = usOI P := by
  obtain ⟨hF, -, hcore⟩ := oi_core P hP
  constructor
  · rintro ⟨hw, hopt⟩
    have h1 := hopt (usOI P, 0) ((feas_OI P a _).2 hF)
    rw [cm_OI, cm_OI] at h1
    exact ((hcore w.1 ((feas_OI P a w).1 hw)).2 (by unfold fOI; simpa using h1))
  · intro e
    refine ⟨(feas_OI P a w).2 (by rw [e]; exact hF), fun w' hw' => ?_⟩
    have := (hcore w'.1 ((feas_OI P a w').1 hw')).1
    rw [cm_OI, cm_OI, e]; unfold fOI at this; linarith

lemma oi_value (P : Params) (hP : P.Standing) (a : ℝ) (w : ℝ × ℝ) (hw : Feasible P a .OI w) :
    cmProfit P a .OI w ≤ fOI P.θ P.c (usOI P) := by
  obtain ⟨-, -, hcore⟩ := oi_core P hP
  have := (hcore w.1 ((feas_OI P a w).1 hw)).1
  rw [cm_OI]; unfold fOI at this ⊢; linarith

/-- Any feasible (I,O) price gives the CM strictly less than the optimal (O,I) profit. -/
lemma io_lt (P : Params) (hP : P.Standing) (a : ℝ) (w : ℝ × ℝ) (hw : Feasible P a .IO w) :
    cmProfit P a .IO w < fOI P.θ P.c (usOI P) := by
  obtain ⟨hc, h1, h2, h3⟩ := standing_facts hP
  obtain ⟨hF, hpos, hcore⟩ := oi_core P hP
  rw [feas_IO] at hw
  rw [cm_IO]
  set v := w.2
  have hP2 : 0 ≤ (2*P.c - 2*v) * (4*P.θ - 2 - 2*v) := by
    have : ((2*P.θ - 1 + P.c - 2*v)/3)^2 - ((2*P.θ - 1 - P.c)/3)^2
        = (2*P.c - 2*v) * (4*P.θ - 2 - 2*v) / 9 := by ring
    linarith
  rcases le_or_gt v 0 with hv | hv
  · have : v * (2*P.θ - 1 + P.c - 2*v) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hv (by linarith)
    linarith
  rcases le_or_gt v P.c with hvc | hvc
  · have hfe : ((2 - P.θ - P.c)/3)^2 ≤ ((2 - P.θ - 2*v + P.c)/3)^2 :=
      sq_le_sq' (by linarith) (by linarith)
    have := (hcore v hfe).1
    unfold fOI at this ⊢
    have : v * (2*P.θ - 1 + P.c - 2*v) < v * (2 - P.θ - 2*v + P.c) :=
      mul_lt_mul_of_pos_left (by linarith) hv
    linarith
  · have hL : 4*P.θ - 2 - 2*v ≤ 0 := by
      by_contra hcon; push Not at hcon
      have := mul_pos (by linarith : (0:ℝ) < 2*v - 2*P.c) hcon
      linarith
    have : v * (2*P.θ - 1 + P.c - 2*v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hv.le (by linarith)
    linarith

lemma oi_star_opt (P : Params) (hP : P.Standing) (a : ℝ) :
    IsOptPrices P a .OI (usOI P, 0) := (oi_opt_iff P hP a _).2 rfl

lemma equilibrium_OO_or_OI (P : Params) (hP : P.Standing) (a : ℝ) (s : Structure)
    (w : ℝ × ℝ) (hs : IsEquilibrium P a s w) : s = .OO ∨ s = .OI := by
  have hopt := oi_star_opt P hP a
  have hval : cmProfit P a .OI (usOI P, 0) = fOI P.θ P.c (usOI P) := by
    rw [cm_OI]; unfold fOI; rfl
  obtain ⟨-, hpos, -⟩ := oi_core P hP
  cases s with
  | OO => exact Or.inl rfl
  | OI => exact Or.inr rfl
  | IO =>
    exfalso
    have h1 := hs.2 .OI _ hopt
    have h2 := io_lt P hP a w hs.1.1
    linarith
  | II =>
    exfalso
    have h1 := hs.2 .OI _ hopt
    rw [cm_II] at h1
    linarith

/-! The committed game (spillover level 0). -/

lemma star_zero (P : Params) :
    usOO P 0 = min P.c (1/2) ∧
    vsOO P 0 = if P.c ≤ 1/2 then min P.c ((2*P.c + 2*P.θ - 1)/4) else P.θ/2 := by
  simp [usOO, vsOO, cOO2]

lemma committed_key (P : Params) (hP : P.Standing) :
    fOI P.θ P.c (usOI P) < cmProfit P 0 .OO (usOO P 0, vsOO P 0) := by
  obtain ⟨hc, h1, h2, h3⟩ := standing_facts hP
  obtain ⟨e1, e2⟩ := star_zero P
  rw [cm_OO]; dsimp only
  simp only [zero_mul, add_zero]
  have hOI : ∀ x : ℝ, (P.c ≤ (2 - P.θ + P.c) / 4 → P.c * (2 - P.θ - 2*P.c + P.c)/3 < x) →
      ((2 - P.θ + P.c) / 4 ≤ P.c →
        (2 - P.θ + P.c) / 4 * (2 - P.θ - 2*((2 - P.θ + P.c) / 4) + P.c)/3 < x) →
      fOI P.θ P.c (usOI P) < x := by
    intro x hA hB
    unfold fOI usOI
    rcases le_total P.c ((2 - P.θ + P.c) / 4) with r' | r'
    · rw [min_eq_left r']; exact hA r'
    · rw [min_eq_right r']; exact hB r'
  apply hOI <;> unfold CMoo
  · intro r'
    rcases le_or_gt P.c ((2*P.θ-1)/2) with r | r
    · rw [e1, e2, min_eq_left (by linarith), if_pos (by linarith), min_eq_left (by linarith)]
      nlinarith [mul_pos hc (by linarith : (0:ℝ) < 2*P.θ-1-P.c)]
    rcases le_or_gt P.c (1/2) with r2 | r2
    · rw [e1, e2, min_eq_left r2, if_pos r2, min_eq_right (by linarith)]
      nlinarith [mul_pos (by linarith : (0:ℝ) < P.c - (2*P.θ-1)/2) (by linarith : (0:ℝ) < P.c - (2*P.θ-1)/2)]
    · exfalso; linarith
  · intro r'
    rcases le_or_gt P.c ((2*P.θ-1)/2) with r | r
    · rw [e1, e2, min_eq_left (by linarith), if_pos (by linarith), min_eq_left (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.c - (2 - P.θ + P.c) / 4)
        (by linarith : (0:ℝ) ≤ (2*P.θ-1)/2 - P.c), mul_pos hc hc]
    rcases le_or_gt P.c (1/2) with r2 | r2
    · rw [e1, e2, min_eq_left r2, if_pos r2, min_eq_right (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.c - (2 - P.θ + P.c) / 4)
        (by linarith : (0:ℝ) ≤ 1/2 - P.c), sq_nonneg (P.c - (2*P.θ-1)/2), mul_pos hc hc]
    · rw [e1, e2, min_eq_right r2.le, if_neg (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.θ - 2/7 - P.c) (by linarith : (0:ℝ) ≤ P.c),
        sq_nonneg (P.θ - 1/2)]

lemma committed_profit (P : Params) (hP : P.Standing) :
    profitW P 0 .OO (usOO P 0, vsOO P 0) =
      if P.c ≤ (2 * P.θ - 1) / 2 then ((2 * P.θ - 1 - P.c) / 3) ^ 2
        else ((2 * P.θ - 1) / 6) ^ 2 := by
  obtain ⟨hc, h1, h2, h3⟩ := standing_facts hP
  obtain ⟨e1, e2⟩ := star_zero P
  rw [profitW_sq, qW_OO]; dsimp only
  rw [e1, e2]
  simp only [zero_mul, add_zero]
  rcases le_or_gt P.c ((2*P.θ-1)/2) with r | r
  · rw [min_eq_left (by linarith), if_pos (by linarith), min_eq_left (by linarith), if_pos r]
    ring
  rcases le_or_gt P.c (1/2) with r2 | r2
  · rw [min_eq_left r2, if_pos r2, min_eq_right (by linarith), if_neg (by linarith)]
    ring
  · rw [min_eq_right r2.le, if_neg (by linarith), if_neg (by linarith)]
    ring

end BSHelp


open BrandSpillover.Commitment BSHelp

set_option maxHeartbeats 2000000 in
/-- The CM strictly prefers (O,O) to (O,I) exactly under conditions (i)–(iii). -/
lemma p3_key (P : Params) (hP : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (((T1 P a < P.c ∧ P.c ≤ cOO1 P a ∧ P.c < cOI P) ∨
        (max (cOO1 P a) (T2 P a) < P.c ∧ P.c < min (cOI P) (T3 P a)) ∨ cOI P ≤ P.c)) ↔
      fOI P.θ P.c (usOI P) < cmProfit P a .OO (usOO P a, vsOO P a) := by
  obtain ⟨hc, h1, h2, h3⟩ := standing_facts hP
  have hb0 : 0 ≤ a*(1-P.θ) := mul_nonneg ha0 (by linarith)
  have hb1 : a*(1-P.θ) ≤ 1 - P.θ := by nlinarith
  rw [cm_OO]; dsimp only
  unfold fOI usOI
  rcases le_or_gt (cOI P) P.c with hiii | hlt
  · refine ⟨fun _ => ?_, fun _ => Or.inr (Or.inr hiii)⟩
    unfold cOI at hiii
    rw [min_eq_right (by linarith)]
    unfold usOO vsOO cOO2 CMoo
    have hhalf : 1/2*a*(1-P.θ) = a*(1-P.θ)/2 := by ring
    rw [hhalf]
    generalize a*(1-P.θ) = b at *
    rcases le_or_gt P.c ((2*P.θ-1-3*b)/2) with r | r
    · rw [min_eq_left (by linarith), if_pos (by linarith), min_eq_left (by linarith)]
      have key : (P.c - b/2) * (2 - (P.θ + b) - 2*(P.c - b/2) + (P.c + b))/3 +
          (P.c + b) * (2*(P.θ + b) - 1 + (P.c - b/2) - 2*(P.c + b))/3 -
          (2 - P.θ + P.c) / 4 * (2 - P.θ - 2*((2 - P.θ + P.c) / 4) + P.c)/3 =
          -(8*b^2 - 20*b*P.θ + 16*b + 17*P.c^2 - 10*P.c*P.θ - 4*P.c + P.θ^2 - 4*P.θ + 4)/24 := by
        ring
      have : 0 < -(8*b^2 - 20*b*P.θ + 16*b + 17*P.c^2 - 10*P.c*P.θ - 4*P.c + P.θ^2 - 4*P.θ + 4) := by
        nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 1 - P.θ - b), mul_nonneg hb0 hb0,
          mul_nonneg (by linarith : (0:ℝ) ≤ (2*P.θ-1-3*b)/2 - P.c)
            (by linarith : (0:ℝ) ≤ P.c - (2-P.θ)/3),
          mul_nonneg (by linarith : (0:ℝ) ≤ (2*P.θ-1-3*b)/2 - P.c) hb0,
          mul_nonneg (by linarith : (0:ℝ) ≤ P.c - (2-P.θ)/3) hb0, mul_pos hc hc]
      linarith
    rcases le_or_gt P.c ((1+b)/2) with r2 | r2
    · rw [min_eq_left (by linarith), if_pos r2, min_eq_right (by linarith)]
      have key : (P.c - b/2) * (2 - (P.θ + b) - 2*(P.c - b/2) + (2*P.c + 2*P.θ - 1 + b)/4)/3 +
          (2*P.c + 2*P.θ - 1 + b)/4 * (2*(P.θ + b) - 1 + (P.c - b/2) - 2*((2*P.c + 2*P.θ - 1 + b)/4))/3 -
          (2 - P.θ + P.c) / 4 * (2 - P.θ - 2*((2 - P.θ + P.c) / 4) + P.c)/3 =
          (b^2 + 12*b*P.c + 8*b*P.θ - 10*b - 13*P.c^2 + 2*P.c*P.θ + 8*P.c + 3*P.θ^2 - 3)/24 := by
        ring
      have : 0 < b^2 + 12*b*P.c + 8*b*P.θ - 10*b - 13*P.c^2 + 2*P.c*P.θ + 8*P.c + 3*P.θ^2 - 3 := by
        nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 1 - P.θ - b), mul_nonneg hb0 hb0,
          mul_nonneg (by linarith : (0:ℝ) ≤ P.θ - 2/7 - P.c) (by linarith : (0:ℝ) ≤ P.c - (2-P.θ)/3),
          mul_nonneg (by linarith : (0:ℝ) ≤ (1+b)/2 - P.c) (by linarith : (0:ℝ) ≤ P.c - (2-P.θ)/3),
          mul_nonneg (by linarith : (0:ℝ) ≤ (1+b)/2 - P.c) hb0, mul_pos hc hc]
      linarith
    · rw [min_eq_right (by linarith), if_neg (by linarith)]
      have key : 1/2 * (2 - (P.θ + b) - 2*(1/2) + (P.θ + b)/2)/3 +
          (P.θ + b)/2 * (2*(P.θ + b) - 1 + 1/2 - 2*((P.θ + b)/2))/3 -
          (2 - P.θ + P.c) / 4 * (2 - P.θ - 2*((2 - P.θ + P.c) / 4) + P.c)/3 =
          (4*b^2 + 8*b*P.θ - 4*b - P.c^2 + 2*P.c*P.θ - 4*P.c + 3*P.θ^2)/24 := by
        ring
      have : 0 < 4*b^2 + 8*b*P.θ - 4*b - P.c^2 + 2*P.c*P.θ - 4*P.c + 3*P.θ^2 := by
        nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 2*P.θ - 1), sq_nonneg (P.θ - 1/2),
          mul_nonneg (by linarith : (0:ℝ) ≤ P.θ - 2/7 - P.c)
            (by linarith : (0:ℝ) ≤ 4 - 2*P.θ + P.c + P.θ - 2/7)]
      linarith
  · have hlt' := hlt
    unfold cOI at hlt'
    rw [min_eq_left (show P.c ≤ (2 - P.θ + P.c) / 4 by linarith)]
    rcases le_or_gt P.c (cOO1 P a) with r1 | r1
    · have hcond : ((T1 P a < P.c ∧ P.c ≤ cOO1 P a ∧ P.c < cOI P) ∨
          (max (cOO1 P a) (T2 P a) < P.c ∧ P.c < min (cOI P) (T3 P a)) ∨ cOI P ≤ P.c) ↔
          T1 P a < P.c := by
        constructor
        · rintro (⟨h, -, -⟩ | ⟨h, -⟩ | h)
          · exact h
          · exact absurd r1 (not_le.mpr (max_lt_iff.1 h).1)
          · exact absurd h (not_le.mpr hlt)
        · intro h; exact Or.inl ⟨h, r1, hlt⟩
      rw [hcond]
      unfold cOO1 at r1
      unfold usOO vsOO cOO2 CMoo T1
      rw [min_eq_left (by linarith), if_pos (by linarith), min_eq_left (by linarith)]
      have key : (P.c - 1/2*a*(1-P.θ)) * (2 - (P.θ + a*(1-P.θ)) - 2*(P.c - 1/2*a*(1-P.θ)) +
            (P.c + a*(1-P.θ)))/3 +
          (P.c + a*(1-P.θ)) * (2*(P.θ + a*(1-P.θ)) - 1 + (P.c - 1/2*a*(1-P.θ)) -
            2*(P.c + a*(1-P.θ)))/3 - P.c * (2 - P.θ - 2*P.c + P.c)/3 =
          (((2 * P.θ - 1) ^ 2 - 4 * a ^ 2 * (1 - P.θ) ^ 2 - 8 * a + 18 * a * P.θ - 10 * a * P.θ ^ 2) - (2*(P.θ - 1/2 - P.c))^2)/12 := by
        ring
      have ht : 0 ≤ 2*(P.θ - 1/2 - P.c) := by nlinarith
      have e : P.θ - 1 / 2 - 1 / 2 * Real.sqrt ((2 * P.θ - 1) ^ 2 - 4 * a ^ 2 * (1 - P.θ) ^ 2 - 8 * a + 18 * a * P.θ - 10 * a * P.θ ^ 2) < P.c ↔ 2*(P.θ - 1/2 - P.c) < Real.sqrt ((2 * P.θ - 1) ^ 2 - 4 * a ^ 2 * (1 - P.θ) ^ 2 - 8 * a + 18 * a * P.θ - 10 * a * P.θ ^ 2) := by
        constructor <;> intro h <;> linarith
      rw [e, Real.lt_sqrt ht]
      have fin : ∀ X Y Z W : ℝ, X - Y = (Z - W)/12 → (W < Z ↔ Y < X) := by
        intro X Y Z W h; constructor <;> intro h' <;> linarith
      exact fin _ _ _ _ key
    rcases le_or_gt P.c (cOO2 P a) with r2 | r2
    · have hcond : ((T1 P a < P.c ∧ P.c ≤ cOO1 P a ∧ P.c < cOI P) ∨
          (max (cOO1 P a) (T2 P a) < P.c ∧ P.c < min (cOI P) (T3 P a)) ∨ cOI P ≤ P.c) ↔
          (T2 P a < P.c ∧ P.c < T3 P a) := by
        constructor
        · rintro (⟨-, h, -⟩ | ⟨h, h'⟩ | h)
          · exact absurd h (not_le.mpr r1)
          · exact ⟨(max_lt_iff.1 h).2, (lt_min_iff.1 h').2⟩
          · exact absurd h (not_le.mpr hlt)
        · rintro ⟨h, h'⟩; exact Or.inr (Or.inl ⟨max_lt r1 h, lt_min hlt h'⟩)
      rw [hcond]
      unfold cOO1 at r1
      unfold cOO2 at r2
      unfold usOO vsOO cOO2 CMoo T2 T3
      rw [min_eq_left (by linarith), if_pos r2, min_eq_right (by linarith)]
      have key : (P.c - 1/2*a*(1-P.θ)) * (2 - (P.θ + a*(1-P.θ)) - 2*(P.c - 1/2*a*(1-P.θ)) +
            (2 * P.c + 2 * P.θ - 1 + a * (1 - P.θ)) / 4)/3 +
          (2 * P.c + 2 * P.θ - 1 + a * (1 - P.θ)) / 4 * (2*(P.θ + a*(1-P.θ)) - 1 +
            (P.c - 1/2*a*(1-P.θ)) - 2*((2 * P.c + 2 * P.θ - 1 + a * (1 - P.θ)) / 4))/3 -
          P.c * (2 - P.θ - 2*P.c + P.c)/3 =
          ((10 * a ^ 2 * (1 - P.θ) ^ 2 + 2 - 8 * P.θ * (1 - P.θ) - 16 * a + 36 * a * P.θ - 20 * a * P.θ ^ 2) - (2*(P.c - (P.θ - 1 / 2 + 3 / 2 * a - 3 / 2 * a * P.θ)))^2)/24 := by
        ring
      have e : ((P.θ - 1 / 2 + 3 / 2 * a - 3 / 2 * a * P.θ) - 1 / 2 * Real.sqrt (10 * a ^ 2 * (1 - P.θ) ^ 2 + 2 - 8 * P.θ * (1 - P.θ) - 16 * a + 36 * a * P.θ - 20 * a * P.θ ^ 2) < P.c ∧ P.c < (P.θ - 1 / 2 + 3 / 2 * a - 3 / 2 * a * P.θ) + 1 / 2 * Real.sqrt (10 * a ^ 2 * (1 - P.θ) ^ 2 + 2 - 8 * P.θ * (1 - P.θ) - 16 * a + 36 * a * P.θ - 20 * a * P.θ ^ 2)) ↔
          |2*(P.c - (P.θ - 1 / 2 + 3 / 2 * a - 3 / 2 * a * P.θ))| < Real.sqrt (10 * a ^ 2 * (1 - P.θ) ^ 2 + 2 - 8 * P.θ * (1 - P.θ) - 16 * a + 36 * a * P.θ - 20 * a * P.θ ^ 2) := by
        rw [abs_lt]; constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
      rw [e, Real.lt_sqrt (abs_nonneg _), sq_abs]
      have fin : ∀ X Y Z W : ℝ, X - Y = (Z - W)/24 → (W < Z ↔ Y < X) := by
        intro X Y Z W h; constructor <;> intro h' <;> linarith
      exact fin _ _ _ _ key
    · exfalso; unfold cOO2 at r2; linarith

theorem solution (P : Params) (hP : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (((T1 P a < P.c ∧ P.c ≤ cOO1 P a ∧ P.c < cOI P) ∨
        (max (cOO1 P a) (T2 P a) < P.c ∧ P.c < min (cOI P) (T3 P a)) ∨ cOI P ≤ P.c) →
      (∃ w : ℝ × ℝ, IsEquilibrium P a .OO w) ∧
      ∀ (s : Structure) (w : ℝ × ℝ), IsEquilibrium P a s w → s = .OO) ∧
    (¬ ((T1 P a < P.c ∧ P.c ≤ cOO1 P a ∧ P.c < cOI P) ∨
        (max (cOO1 P a) (T2 P a) < P.c ∧ P.c < min (cOI P) (T3 P a)) ∨ cOI P ≤ P.c) →
      ∃ w : ℝ × ℝ, IsEquilibrium P a .OI w) := by
  have hstar : IsOptPrices P a .OO (usOO P a, vsOO P a) :=
    (oo_opt_iff P hP a ha0 ha1 _).2 ⟨rfl, rfl⟩
  have hkey := p3_key P hP a ha0 ha1
  obtain ⟨-, hpos, -⟩ := oi_core P hP
  have hoi := oi_star_opt P hP a
  have hoival : cmProfit P a .OI (usOI P, 0) = fOI P.θ P.c (usOI P) := by
    rw [cm_OI]; unfold fOI; rfl
  constructor
  · intro hcond
    have hlt := hkey.1 hcond
    have hdom : ∀ (s' : Structure) (w' : ℝ × ℝ), IsOptPrices P a s' w' →
        cmProfit P a s' w' ≤ cmProfit P a .OO (usOO P a, vsOO P a) := by
      intro s' w' h
      cases s' with
      | OO => exact hstar.2 w' h.1
      | OI => linarith [oi_value P hP a w' h.1]
      | IO => linarith [io_lt P hP a w' h.1]
      | II => rw [cm_II]; linarith
    refine ⟨⟨_, hstar, hdom⟩, fun s w hs => ?_⟩
    rcases equilibrium_OO_or_OI P hP a s w hs with h | rfl
    · exact h
    · exfalso
      have h1 := hs.2 .OO _ hstar
      have h2 := oi_value P hP a w hs.1.1
      linarith
  · intro hcond
    have hle : cmProfit P a .OO (usOO P a, vsOO P a) ≤ fOI P.θ P.c (usOI P) :=
      not_lt.mp (fun h => hcond (hkey.2 h))
    refine ⟨_, hoi, fun s' w' h => ?_⟩
    rw [hoival]
    cases s' with
    | OO => linarith [hstar.2 w' h.1]
    | OI => exact oi_value P hP a w' h.1
    | IO => linarith [io_lt P hP a w' h.1]
    | II => rw [cm_II]; linarith
