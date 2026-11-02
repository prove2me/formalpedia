-- Prove2me | solution 1 for EcoOffset.Subgame.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:31:09.821343+00:00
-- url     : https://prove2.me/submissions/9d109cb7-fa16-4eef-9de8-2b282626cdb7

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model
import Theorems.Thm_EcoOffset_Subgame_segOpt_spec
import Theorems.Thm_EcoOffset_Subgame_caseN_reduction
import Theorems.Thm_EcoOffset_Subgame_caseP_reduction

namespace EcoPropAux
open EcoOffset.Subgame

/-- The derivative of `segObj P x a` in `e`. -/
noncomputable def Dseg (P : Params) (x a e : ℝ) : ℝ :=
  -(deriv P.c e + x) * a * P.m - deriv P.f e

theorem hasDerivAt_segObj (P : Params) (hS : P.Standing) (x a e : ℝ) :
    HasDerivAt (segObj P x a) (Dseg P x a e) e := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS
  have hcd : Differentiable ℝ P.c := hc2.differentiable (by norm_num)
  have hfd : Differentiable ℝ P.f := hf2.differentiable (by norm_num)
  have h : HasDerivAt (fun y => -(P.c y + x * y) * a * P.m - P.f y)
      (-(deriv P.c e + x * 1) * a * P.m - deriv P.f e) e := by
    apply HasDerivAt.sub _ (hfd e).hasDerivAt
    apply HasDerivAt.mul_const
    apply HasDerivAt.mul_const
    apply HasDerivAt.neg
    exact (hcd e).hasDerivAt.add ((hasDerivAt_id e).const_mul x)
  show HasDerivAt (fun y => -(P.c y + x * y) * a * P.m - P.f y) _ e
  convert h using 1
  simp [Dseg]

theorem continuous_segObj (P : Params) (hS : P.Standing) (x a : ℝ) :
    Continuous (segObj P x a) :=
  continuous_iff_continuousAt.2 fun e => (hasDerivAt_segObj P hS x a e).continuousAt

theorem deriv_strictMonoOn (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (ebar : ℝ)
    (h : ∀ e ∈ Set.Icc 0 ebar, 0 < deriv (deriv g) e) :
    StrictMonoOn (deriv g) (Set.Icc 0 ebar) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 ebar)
  · exact (hg.continuous_deriv (by norm_num)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact h x (Set.Ioo_subset_Icc_self hx)

theorem Dseg_strictAnti (P : Params) (hS : P.Standing) (x a : ℝ) (ha : 0 ≤ a) {e1 e2 : ℝ}
    (h1 : e1 ∈ Set.Icc 0 P.ebar) (h2 : e2 ∈ Set.Icc 0 P.ebar) (h12 : e1 < e2) :
    Dseg P x a e2 < Dseg P x a e1 := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS
  have hc := deriv_strictMonoOn P.c hc2 P.ebar (fun e he => (hder e he).2.1) h1 h2 h12
  have hf := deriv_strictMonoOn P.f hf2 P.ebar (fun e he => (hder e he).2.2.2) h1 h2 h12
  have : 0 ≤ (deriv P.c e2 - deriv P.c e1) * a * P.m := by
    have : 0 ≤ deriv P.c e2 - deriv P.c e1 := by linarith
    positivity
  unfold Dseg
  nlinarith

/-- If the derivative is nonnegative at the right end `v`, `segObj` strictly increases on `[u,v]`. -/
theorem segObj_lt_of_Dseg_nonneg (P : Params) (hS : P.Standing) (x a : ℝ) (ha : 0 ≤ a)
    {u v : ℝ} (hu : u ∈ Set.Icc 0 P.ebar) (hv : v ∈ Set.Icc 0 P.ebar) (huv : u < v)
    (hD : 0 ≤ Dseg P x a v) : segObj P x a u < segObj P x a v := by
  have hmono : StrictMonoOn (segObj P x a) (Set.Icc u v) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc u v)
    · exact (continuous_segObj P hS x a).continuousOn
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hasDerivAt_segObj P hS x a w).deriv]
      have hw' : w ∈ Set.Icc 0 P.ebar := ⟨by linarith [hu.1, hw.1], by linarith [hv.2, hw.2]⟩
      have := Dseg_strictAnti P hS x a ha hw' hv hw.2
      linarith
  exact hmono (Set.left_mem_Icc.2 huv.le) (Set.right_mem_Icc.2 huv.le) huv

/-- If the derivative is nonpositive at the left end `u`, `segObj` strictly decreases on `[u,v]`. -/
theorem segObj_lt_of_Dseg_nonpos (P : Params) (hS : P.Standing) (x a : ℝ) (ha : 0 ≤ a)
    {u v : ℝ} (hu : u ∈ Set.Icc 0 P.ebar) (hv : v ∈ Set.Icc 0 P.ebar) (huv : u < v)
    (hD : Dseg P x a u ≤ 0) : segObj P x a v < segObj P x a u := by
  have hanti : StrictAntiOn (segObj P x a) (Set.Icc u v) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc u v)
    · exact (continuous_segObj P hS x a).continuousOn
    · intro w hw
      rw [interior_Icc] at hw
      rw [(hasDerivAt_segObj P hS x a w).deriv]
      have hw' : w ∈ Set.Icc 0 P.ebar := ⟨by linarith [hu.1, hw.1], by linarith [hv.2, hw.2]⟩
      have := Dseg_strictAnti P hS x a ha hu hw' hw.1
      linarith
  exact hanti (Set.left_mem_Icc.2 huv.le) (Set.right_mem_Icc.2 huv.le) huv

theorem isSegOpt_segOpt' (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) : IsSegOpt P x a (segOpt P x a) :=
  (segOpt_spec P hS x a hx ha0 ha1).1

theorem le_segOpt (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) {e : ℝ} (he : e ∈ Set.Icc 0 P.ebar) (hD : 0 ≤ Dseg P x a e) :
    e ≤ segOpt P x a := by
  have hs := isSegOpt_segOpt' P hS x a hx ha ha1
  by_contra hlt
  push Not at hlt
  have := segObj_lt_of_Dseg_nonneg P hS x a ha hs.1 he hlt hD
  linarith [hs.2 e he]

theorem segOpt_le (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) {e : ℝ} (he : e ∈ Set.Icc 0 P.ebar) (hD : Dseg P x a e ≤ 0) :
    segOpt P x a ≤ e := by
  have hs := isSegOpt_segOpt' P hS x a hx ha ha1
  by_contra hlt
  push Not at hlt
  have := segObj_lt_of_Dseg_nonpos P hS x a ha he hs.1 hlt hD
  linarith [hs.2 e he]

theorem Dseg_shift (P : Params) (x y a e : ℝ) :
    Dseg P y a e = Dseg P x a e + (x - y) * a * P.m := by
  unfold Dseg; ring

theorem continuous_Dseg (P : Params) (hS : P.Standing) (x a : ℝ) :
    Continuous (fun e => Dseg P x a e) := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS
  have h1 := hc2.continuous_deriv (by norm_num)
  have h2 := hf2.continuous_deriv (by norm_num)
  unfold Dseg
  fun_prop

/-- `Dseg P 0 1 e = -c'(e) m - f'(e) > 0` on `[0, ¯e]`. -/
theorem Dseg_zero_pos (P : Params) (hS : P.Standing) (e : ℝ) (he : e ∈ Set.Icc 0 P.ebar) :
    0 < Dseg P 0 1 e := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS
  obtain ⟨h1, -, h3, -⟩ := hder e he
  unfold Dseg
  have : 0 < -(deriv P.c e + 0) * 1 * P.m := by
    have : 0 < -(deriv P.c e + 0) := by linarith
    positivity
  linarith

/-- If `Dseg P X a e = ... ≤ 0`-type comparison: when `Dseg P X a e ≤ 0` with `a < 1`, then
`Dseg P X 1 e < 0`. -/
theorem Dseg_one_neg (P : Params) (hS : P.Standing) (X a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (e : ℝ) (he : e ∈ Set.Icc 0 P.ebar) (hD : Dseg P X a e ≤ 0) : Dseg P X 1 e < 0 := by
  have hS' := hS
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS'
  obtain ⟨h1, -, h3, -⟩ := hder e he
  unfold Dseg at *
  have hpos : 0 < (deriv P.c e + X) * a * P.m := by linarith
  have hcX : 0 < deriv P.c e + X := by
    by_contra h
    push Not at h
    have : (deriv P.c e + X) * a * P.m ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg h ha0
      exact mul_nonpos_of_nonpos_of_nonneg this hm.le
    linarith
  have : 0 < (deriv P.c e + X) * (1 - a) * P.m := by
    have : 0 < 1 - a := by linarith
    positivity
  nlinarith

/-- Continuity: a strict negative value of `Dseg P X 1` at `e0 > 0` persists at a smaller point. -/
theorem exists_lt_neg (P : Params) (hS : P.Standing) (X : ℝ) (e0 : ℝ) (he0 : 0 < e0)
    (hD : Dseg P X 1 e0 < 0) : ∃ e, 0 < e ∧ e < e0 ∧ Dseg P X 1 e < 0 := by
  have hc := (continuous_Dseg P hS X 1).continuousAt (x := e0)
  have hev : ∀ᶠ e in nhds e0, Dseg P X 1 e < 0 := hc.eventually_lt continuousAt_const hD
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨max (e0 / 2) (e0 - δ / 2), lt_max_of_lt_left (by linarith),
    max_lt (by linarith) (by linarith), hball ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := le_max_right (e0 / 2) (e0 - δ / 2); linarith
  · have := max_lt (show e0 / 2 < e0 by linarith) (show e0 - δ / 2 < e0 by linarith); linarith

/-- Helper H: choose `g1 ∈ (0, X)` with `e_hi/2 ≤ e_{g1,1} ≤ e_hi`. -/
theorem exists_g1 (P : Params) (hS : P.Standing) (X : ℝ) (hX : 0 < X) (ehi : ℝ)
    (hehi : 0 < ehi) (hehi' : ehi ≤ P.ebar) (hD : Dseg P X 1 ehi < 0) :
    ∃ g1, 0 < g1 ∧ g1 < X ∧ ehi / 2 ≤ segOpt P g1 1 ∧ segOpt P g1 1 ≤ ehi := by
  have hm : 0 < P.m := hS.1
  have hm1 : ehi ∈ Set.Icc 0 P.ebar := ⟨hehi.le, hehi'⟩
  have hm2 : ehi / 2 ∈ Set.Icc 0 P.ebar := ⟨by linarith, by linarith⟩
  set A := Dseg P 0 1 ehi with hA
  set B := Dseg P 0 1 (ehi / 2) with hB
  have hA0 : 0 < A := Dseg_zero_pos P hS ehi hm1
  have hAB : A < B := Dseg_strictAnti P hS 0 1 zero_le_one hm2 hm1 (by linarith)
  have hAX : A < X * P.m := by
    have := Dseg_shift P 0 X 1 ehi
    rw [← hA] at this
    nlinarith
  set g1 := (A + min B (X * P.m)) / (2 * P.m) with hg1
  have hmin1 := min_le_left B (X * P.m)
  have hmin2 := min_le_right B (X * P.m)
  have hmin3 : A < min B (X * P.m) := lt_min hAB hAX
  have hg1m : g1 * P.m = (A + min B (X * P.m)) / 2 := by rw [hg1]; field_simp
  have hg1pos : 0 < g1 := by rw [hg1]; apply div_pos (by linarith) (by linarith)
  refine ⟨g1, hg1pos, ?_, ?_, ?_⟩
  · by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_right h hm.le
    linarith
  · apply le_segOpt P hS g1 1 hg1pos.le zero_le_one le_rfl hm2
    have := Dseg_shift P 0 g1 1 (ehi / 2)
    rw [← hB] at this
    nlinarith
  · apply segOpt_le P hS g1 1 hg1pos.le zero_le_one le_rfl hm1
    have := Dseg_shift P 0 g1 1 ehi
    rw [← hA] at this
    nlinarith

/-- The common choice from two points `e_hi < e_up`. -/
theorem choice_main (P : Params) (hS : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (X : ℝ) (hX : 0 < X) (ehi eup : ℝ) (hehi : 0 < ehi) (hlt : ehi < eup) (hup : eup ≤ P.ebar)
    (hD1 : Dseg P X 1 ehi < 0) (hDa : 0 < Dseg P X a eup) :
    ∃ g1 η, 0 < g1 ∧ g1 < X ∧ 0 < η ∧
      (∀ g2, X < g2 → g2 < X + η → segOpt P g1 1 < segOpt P g2 a) ∧
      0 < segOpt P g1 1 := by
  have hm : 0 < P.m := hS.1
  obtain ⟨g1, hg1, hg1X, hlo, hhi⟩ := exists_g1 P hS X hX ehi hehi (by linarith) hD1
  refine ⟨g1, Dseg P X a eup / P.m, hg1, hg1X, div_pos hDa hm, ?_, by linarith⟩
  intro g2 hXg2 hg2
  have hup' : eup ∈ Set.Icc 0 P.ebar := ⟨by linarith, hup⟩
  have : eup ≤ segOpt P g2 a := by
    apply le_segOpt P hS g2 a (by linarith) ha0 ha1.le hup'
    rw [Dseg_shift P X g2 a eup]
    have h1 : (g2 - X) * P.m < Dseg P X a eup := by
      have : g2 - X < Dseg P X a eup / P.m := by linarith
      rwa [lt_div_iff₀ hm] at this
    have h2 : (g2 - X) * a * P.m ≤ (g2 - X) * P.m := by
      have : 0 ≤ g2 - X := by linarith
      have : (g2 - X) * a ≤ (g2 - X) * 1 := mul_le_mul_of_nonneg_left ha1.le this
      nlinarith
    nlinarith
  linarith

/-- The generic choice of `g1 < X < g2` for both cases of Proposition 1. -/
theorem choose_pair (P : Params) (hS : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (X : ℝ) (hX : 0 < X) :
    ∃ g1 η, 0 < g1 ∧ g1 < X ∧ 0 < η ∧
      (∀ g2, X < g2 → g2 < X + η →
        segOpt P g1 1 ≤ segOpt P g2 a ∧
        (segOpt P X 1 < P.ebar → 0 < segOpt P X a → segOpt P g1 1 < segOpt P g2 a)) ∧
      ((0 < segOpt P g1 1 ∧ ∀ g2, X < g2 → g2 < X + η → 0 < segOpt P g2 a) ∨
        (∀ g, X ≤ g → segOpt P g 1 = 0 ∧ segOpt P g a = 0)) := by
  have hm : 0 < P.m := hS.1
  have heb : 0 < P.ebar := hS.2.1
  have hebar : P.ebar ∈ Set.Icc 0 P.ebar := ⟨heb.le, le_rfl⟩
  have h0 : (0:ℝ) ∈ Set.Icc 0 P.ebar := ⟨le_rfl, heb.le⟩
  -- packaging the main case
  have fromMain : ∀ ehi eup, 0 < ehi → ehi < eup → eup ≤ P.ebar → Dseg P X 1 ehi < 0 →
      0 < Dseg P X a eup →
      ∃ g1 η, 0 < g1 ∧ g1 < X ∧ 0 < η ∧
      (∀ g2, X < g2 → g2 < X + η →
        segOpt P g1 1 ≤ segOpt P g2 a ∧
        (segOpt P X 1 < P.ebar → 0 < segOpt P X a → segOpt P g1 1 < segOpt P g2 a)) ∧
      ((0 < segOpt P g1 1 ∧ ∀ g2, X < g2 → g2 < X + η → 0 < segOpt P g2 a) ∨
        (∀ g, X ≤ g → segOpt P g 1 = 0 ∧ segOpt P g a = 0)) := by
    intro ehi eup h1 h2 h3 h4 h5
    obtain ⟨g1, η, hg1, hg1X, hη, hcmp, hpos⟩ :=
      choice_main P hS a ha0 ha1 X hX ehi eup h1 h2 h3 h4 h5
    refine ⟨g1, η, hg1, hg1X, hη, fun g2 hg2 hg2' => ⟨(hcmp g2 hg2 hg2').le,
      fun _ _ => hcmp g2 hg2 hg2'⟩, Or.inl ⟨hpos, fun g2 hg2 hg2' => ?_⟩⟩
    linarith [hcmp g2 hg2 hg2']
  rcases lt_or_ge 0 (Dseg P X a P.ebar) with hA | hB
  · -- Case A
    rcases le_or_gt 0 (Dseg P X 1 P.ebar) with hA1 | hA2
    · refine ⟨X / 2, Dseg P X a P.ebar / P.m, by linarith, by linarith, div_pos hA hm, ?_, ?_⟩
      · have he1 : segOpt P (X / 2) 1 = P.ebar := by
          apply le_antisymm
            (isSegOpt_segOpt' P hS (X / 2) 1 (by linarith) zero_le_one le_rfl).1.2
          apply le_segOpt P hS (X / 2) 1 (by linarith) zero_le_one le_rfl hebar
          rw [Dseg_shift P X (X / 2) 1 P.ebar]
          have : 0 ≤ (X - X / 2) * 1 * P.m := by
            have : 0 ≤ X - X / 2 := by linarith
            positivity
          linarith
        have hX1 : segOpt P X 1 = P.ebar := by
          apply le_antisymm (isSegOpt_segOpt' P hS X 1 hX.le zero_le_one le_rfl).1.2
          exact le_segOpt P hS X 1 hX.le zero_le_one le_rfl hebar hA1
        intro g2 hXg2 hg2
        have he2 : segOpt P g2 a = P.ebar := by
          apply le_antisymm (isSegOpt_segOpt' P hS g2 a (by linarith) ha0 ha1.le).1.2
          apply le_segOpt P hS g2 a (by linarith) ha0 ha1.le hebar
          rw [Dseg_shift P X g2 a P.ebar]
          have h1 : (g2 - X) * P.m < Dseg P X a P.ebar := by
            have : g2 - X < Dseg P X a P.ebar / P.m := by linarith
            rwa [lt_div_iff₀ hm] at this
          have h2 : (g2 - X) * a * P.m ≤ (g2 - X) * P.m := by
            have : 0 ≤ g2 - X := by linarith
            have : (g2 - X) * a ≤ (g2 - X) * 1 := mul_le_mul_of_nonneg_left ha1.le this
            nlinarith
          nlinarith
        rw [he1, he2, hX1]
        exact ⟨le_rfl, fun h _ => absurd h (lt_irrefl _)⟩
      · left
        have he1 : segOpt P (X / 2) 1 = P.ebar := by
          apply le_antisymm
            (isSegOpt_segOpt' P hS (X / 2) 1 (by linarith) zero_le_one le_rfl).1.2
          apply le_segOpt P hS (X / 2) 1 (by linarith) zero_le_one le_rfl hebar
          rw [Dseg_shift P X (X / 2) 1 P.ebar]
          have : 0 ≤ (X - X / 2) * 1 * P.m := by
            have : 0 ≤ X - X / 2 := by linarith
            positivity
          linarith
        refine ⟨by rw [he1]; exact heb, fun g2 hXg2 hg2 => ?_⟩
        have : P.ebar ≤ segOpt P g2 a := by
          apply le_segOpt P hS g2 a (by linarith) ha0 ha1.le hebar
          rw [Dseg_shift P X g2 a P.ebar]
          have h1 : (g2 - X) * P.m < Dseg P X a P.ebar := by
            have : g2 - X < Dseg P X a P.ebar / P.m := by linarith
            rwa [lt_div_iff₀ hm] at this
          have h2 : (g2 - X) * a * P.m ≤ (g2 - X) * P.m := by
            have : 0 ≤ g2 - X := by linarith
            have : (g2 - X) * a ≤ (g2 - X) * 1 := mul_le_mul_of_nonneg_left ha1.le this
            nlinarith
          nlinarith
        linarith
    · obtain ⟨ehi, h1, h2, h3⟩ := exists_lt_neg P hS X P.ebar heb hA2
      exact fromMain ehi P.ebar h1 h2 le_rfl h3 hA
  · rcases le_or_gt (Dseg P X a 0) 0 with hdeg | hmain
    · -- degenerate case
      have hD10 : Dseg P X 1 0 < 0 := Dseg_one_neg P hS X a ha0 ha1 0 h0 hdeg
      have hall : ∀ g, X ≤ g → segOpt P g 1 = 0 ∧ segOpt P g a = 0 := by
        intro g hg
        constructor
        · apply le_antisymm _ (isSegOpt_segOpt' P hS g 1 (by linarith) zero_le_one le_rfl).1.1
          apply segOpt_le P hS g 1 (by linarith) zero_le_one le_rfl h0
          rw [Dseg_shift P X g 1 0]
          have : 0 ≤ (g - X) * 1 * P.m := by
            have : 0 ≤ g - X := by linarith
            positivity
          linarith
        · apply le_antisymm _ (isSegOpt_segOpt' P hS g a (by linarith) ha0 ha1.le).1.1
          apply segOpt_le P hS g a (by linarith) ha0 ha1.le h0
          rw [Dseg_shift P X g a 0]
          have : 0 ≤ (g - X) * a * P.m := by
            have : 0 ≤ g - X := by linarith
            positivity
          linarith
      set δ := min (X / 2) (-(Dseg P X 1 0) / (2 * P.m)) with hδ
      have hδpos : 0 < δ := lt_min (by linarith) (div_pos (by linarith) (by linarith))
      have hδ1 := min_le_left (X / 2) (-(Dseg P X 1 0) / (2 * P.m))
      have hδ2 := min_le_right (X / 2) (-(Dseg P X 1 0) / (2 * P.m))
      have he1 : segOpt P (X - δ) 1 = 0 := by
        apply le_antisymm _
          (isSegOpt_segOpt' P hS (X - δ) 1 (by linarith) zero_le_one le_rfl).1.1
        apply segOpt_le P hS (X - δ) 1 (by linarith) zero_le_one le_rfl h0
        rw [Dseg_shift P X (X - δ) 1 0]
        have : δ * (2 * P.m) ≤ -(Dseg P X 1 0) := by
          rw [le_div_iff₀ (by linarith)] at hδ2; exact hδ2
        nlinarith
      have hX0 := (hall X le_rfl).2
      refine ⟨X - δ, 1, by linarith, by linarith, one_pos, fun g2 hXg2 _ => ?_, Or.inr hall⟩
      rw [he1, (hall g2 hXg2.le).2, hX0]
      exact ⟨le_rfl, fun _ h => absurd h (lt_irrefl _)⟩
    · -- main case: IVT
      have hcont := (continuous_Dseg P hS X a).continuousOn (s := Set.Icc 0 P.ebar)
      have hivt := intermediate_value_Icc' heb.le hcont
      obtain ⟨eN, heN, heN0⟩ := hivt ⟨hB, hmain.le⟩
      have heNpos : 0 < eN := by
        rcases heN.1.lt_or_eq with h | h
        · exact h
        · rw [← h] at heN0; simp only at heN0; linarith
      have hD1N : Dseg P X 1 eN < 0 :=
        Dseg_one_neg P hS X a ha0 ha1 eN heN (by simp only at heN0; linarith)
      obtain ⟨ehi, h1, h2, h3⟩ := exists_lt_neg P hS X eN heNpos hD1N
      have hup : (ehi + eN) / 2 ∈ Set.Icc 0 P.ebar := ⟨by linarith, by linarith [heN.2]⟩
      have hDup : 0 < Dseg P X a ((ehi + eN) / 2) := by
        have := Dseg_strictAnti P hS X a ha0 hup heN (by linarith)
        simp only at heN0
        linarith
      exact fromMain ehi ((ehi + eN) / 2) h1 (by linarith) hup.2 h3 hDup

end EcoPropAux

open EcoOffset.Subgame EcoPropAux in
theorem solution (P : Params) (hS : P.Standing) :
    -- (i) Case N
    (P.βu = 1 → 0 < P.α → P.βc < B2 P →
      ∀ X : ℝ, 0 < X → hN P X = 0 → (∀ g ∈ Set.Ico 0 X, 0 < hN P g) →
      (∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), hN P g < 0) →
      X < P.ξ →
      valOne P < valAll P X →
      ∃ g1 g2 : ℝ, 0 < g1 ∧ g1 < g2 ∧
        (∃ p e t, IsBestResponse P g1 p e t) ∧ (∃ p e t, IsBestResponse P g2 p e t) ∧
        ∀ p1 e1 t1 p2 e2 t2, IsBestResponse P g1 p1 e1 t1 → IsBestResponse P g2 p2 e2 t2 →
          0 < t1 ∧ 0 < t2 ∧ e1 ≤ e2 ∧
          demandU P p1 e1 t1 = demandU P p2 e2 t2 ∧
          demandC P p2 e2 t2 < demandC P p1 e1 t1 ∧
          (segOpt P X 1 < P.ebar → 0 < segOpt P X (aN P) → e1 < e2)) ∧
    -- (ii) Case P
    (P.βc = 1 → P.α < 1 → P.vh - P.vl < P.ξ * P.eo → P.βu < B2P P →
      ∀ X : ℝ, 0 < X → hP P X = 0 → (∀ g ∈ Set.Ico 0 X, 0 < hP P g) →
      (∀ ε > 0, ∃ g ∈ Set.Ioo X (X + ε), hP P g < 0) →
      X < P.ξ →
      max (valOne P) (valThree P) < valTwoP P X →
      ∃ g1 g2 : ℝ, 0 < g1 ∧ g1 < g2 ∧
        (∃ p e t, IsBestResponse P g1 p e t) ∧ (∃ p e t, IsBestResponse P g2 p e t) ∧
        ∀ p1 e1 t1 p2 e2 t2, IsBestResponse P g1 p1 e1 t1 → IsBestResponse P g2 p2 e2 t2 →
          0 < t1 ∧ 0 < t2 ∧ e1 ≤ e2 ∧
          demandC P p1 e1 t1 = demandC P p2 e2 t2 ∧
          demandU P p2 e2 t2 < demandU P p1 e1 t1 ∧
          (segOpt P X 1 < P.ebar → 0 < segOpt P X (aP P) → e1 < e2)) := by
  have hS' := hS
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS'
  have hK : 0 < P.vh - P.c P.ebar := by linarith
  have hL : 0 < (P.ebar + P.eo) * P.m := by positivity
  constructor
  · ---------------- Case N
    intro hβu hα hB2 X hX hX0 hXmin hsign hXξ hcond
    have hB2lt : B2 P < 1 := by
      unfold B2
      rw [div_lt_one hα]
      have : (P.vl - P.c P.ebar) / (P.vh - P.c P.ebar) < 1 := by
        rw [div_lt_one hK]; linarith
      linarith
    have hβc' : P.βc < 1 := by linarith
    have haN0 : 0 ≤ aN P := by
      unfold aN; have := mul_nonneg hα0 hβc0; linarith
    have haN1 : aN P < 1 := by
      unfold aN; have := mul_lt_mul_of_pos_left hβc' hα; linarith
    obtain ⟨g1, η, hg1, hg1X, hη, hcmp, hpos⟩ := choose_pair P hS (aN P) haN0 haN1 X hX
    -- lower bound for `valAll`
    set sX := segOpt P X 1 with hsX
    have hsXm : sX ∈ Set.Icc 0 P.ebar := (isSegOpt_segOpt' P hS X 1 hX.le zero_le_one le_rfl).1
    have hlow : ∀ g, 0 ≤ g →
        valAll P X - (g - X) * (sX + P.eo) * P.m ≤ valAll P g := by
      intro g hg
      have h1 := (isSegOpt_segOpt' P hS g 1 hg zero_le_one le_rfl).2 sX hsXm
      have h2 : valAll P g - (valAll P X - (g - X) * (sX + P.eo) * P.m) =
          segObj P g 1 (segOpt P g 1) - segObj P g 1 sX := by
        unfold valAll segObj; rw [← hsX]; ring
      linarith
    set Δ := valAll P X - valOne P with hΔ
    have hΔ0 : 0 < Δ := by linarith
    set ε := min η (min (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m))) with hε
    have hε0 : 0 < ε := lt_min hη (lt_min (by linarith) (div_pos hΔ0 hL))
    obtain ⟨g2, ⟨hXg2, hg2ε⟩, hneg⟩ := hsign ε hε0
    have hε1 := min_le_left η (min (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m)))
    have hε2 := min_le_right η (min (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m)))
    have hε3 := min_le_left (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m))
    have hε4 := min_le_right (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m))
    have hg2η : g2 < X + η := by linarith
    have hg2ξ : g2 < P.ξ := by linarith
    have hval2 : valOne P < valAll P g2 := by
      have hlo := hlow g2 (by linarith)
      have h1 : (g2 - X) * ((P.ebar + P.eo) * P.m) < Δ := by
        have : g2 - X < Δ / ((P.ebar + P.eo) * P.m) := by linarith
        rwa [lt_div_iff₀ hL] at this
      have h2 : (g2 - X) * (sX + P.eo) * P.m ≤ (g2 - X) * ((P.ebar + P.eo) * P.m) := by
        have : 0 ≤ g2 - X := by linarith
        have : (sX + P.eo) * P.m ≤ (P.ebar + P.eo) * P.m :=
          mul_le_mul_of_nonneg_right (by linarith [hsXm.2]) hm.le
        nlinarith
      linarith
    have hval1 : valOne P < valAll P g1 := by
      have hlo := hlow g1 hg1.le
      have : 0 ≤ (X - g1) * (sX + P.eo) * P.m := by
        have : 0 ≤ X - g1 := by linarith
        have : 0 ≤ sX + P.eo := by linarith [hsXm.1]
        positivity
      linarith
    have hN1 : 0 < hN P g1 := hXmin g1 ⟨hg1.le, hg1X⟩
    unfold hN at hN1 hneg
    obtain ⟨-, hR1, -, hd1, -⟩ := caseN_reduction P hS hβu g1 hg1 (by linarith)
    obtain ⟨-, -, hR2, -, hd2⟩ := caseN_reduction P hS hβu g2 (by linarith) hg2ξ
    have hBR1 := hR1 (max_lt hval1 (by linarith))
    have hBR2 := hR2 (max_lt (by linarith) (by linarith))
    refine ⟨g1, g2, hg1, by linarith, ⟨_, _, _, (hBR1 _ _ _).2 ⟨rfl, rfl, rfl⟩⟩,
      ⟨_, _, _, (hBR2 _ _ _).2 ⟨rfl, rfl, rfl⟩⟩, ?_⟩
    intro p1 e1 t1 p2 e2 t2 h1 h2
    obtain ⟨rfl, rfl, rfl⟩ := (hBR1 _ _ _).1 h1
    obtain ⟨rfl, rfl, rfl⟩ := (hBR2 _ _ _).1 h2
    obtain ⟨hle, hstrict⟩ := hcmp g2 hXg2 hg2η
    have hs1 : 0 ≤ segOpt P g1 1 :=
      (isSegOpt_segOpt' P hS g1 1 hg1.le zero_le_one le_rfl).1.1
    have hs2 : 0 ≤ segOpt P g2 (aN P) :=
      (isSegOpt_segOpt' P hS g2 (aN P) (by linarith) haN0 haN1.le).1.1
    have ht : 0 < segOpt P g1 1 + P.eo ∧ 0 < segOpt P g2 (aN P) + P.eo := by
      rcases hpos with ⟨hp1, hp2⟩ | hall
      · exact ⟨by linarith, by linarith [hp2 g2 hXg2 hg2η]⟩
      · rcases heo.lt_or_eq with heo' | heo'
        · constructor <;> linarith
        · exfalso
          -- with `eo = 0`, `h` is constant on `[X, ∞)`
          have hXa := hall X le_rfl
          have hg2a := hall g2 hXg2.le
          have hNX : hN P X = valAll P X - valTwoN P X := rfl
          unfold valAll valTwoN at hneg hNX
          rw [hg2a.1, hg2a.2, ← heo'] at hneg
          rw [hXa.1, hXa.2, ← heo'] at hNX
          have : hN P X = valAll P g2 - valTwoN P g2 := by
            unfold valAll valTwoN; rw [hNX, hg2a.1, hg2a.2, ← heo']; ring
          linarith
    refine ⟨ht.1, ht.2, hle, ?_, ?_, hstrict⟩
    · rw [hd1.2, hd2.2]
    · rw [hd1.1, hd2.1]
      have : 0 < P.α * P.m * (1 - P.βc) := by
        have : 0 < 1 - P.βc := by linarith
        positivity
      nlinarith
  · ---------------- Case P
    intro hβc hα hv hB2 X hX hX0 hXmin hsign hXξ hcond
    have heo0 : 0 < P.eo := by
      by_contra h; push Not at h
      have := mul_le_mul_of_nonneg_left h hξ.le
      linarith
    have hden : 0 < P.ξ * P.eo * (1 - P.α) := by
      have : 0 < 1 - P.α := by linarith
      positivity
    have hB2lt : B2P P < 1 := by
      unfold B2P
      apply lt_of_le_of_lt (min_le_right _ _)
      rw [div_lt_one hden]; linarith
    have hβu' : P.βu < 1 := by linarith
    have haP0 : 0 ≤ aP P := by
      unfold aP; have := mul_nonneg (show (0:ℝ) ≤ 1 - P.α by linarith) hβu0; linarith
    have haP1 : aP P < 1 := by
      unfold aP
      have := mul_lt_mul_of_pos_left hβu' (show (0:ℝ) < 1 - P.α by linarith)
      linarith
    obtain ⟨g1, η, hg1, hg1X, hη, hcmp, hpos⟩ := choose_pair P hS (aP P) haP0 haP1 X hX
    set sX := segOpt P X (aP P) with hsX
    have hsXm : sX ∈ Set.Icc 0 P.ebar :=
      (isSegOpt_segOpt' P hS X (aP P) hX.le haP0 haP1.le).1
    have hlow : ∀ g, 0 ≤ g →
        valTwoP P X - (g - X) * (sX + P.eo) * aP P * P.m ≤ valTwoP P g := by
      intro g hg
      have h1 := (isSegOpt_segOpt' P hS g (aP P) hg haP0 haP1.le).2 sX hsXm
      have h2 : valTwoP P g - (valTwoP P X - (g - X) * (sX + P.eo) * aP P * P.m) =
          segObj P g (aP P) (segOpt P g (aP P)) - segObj P g (aP P) sX := by
        unfold valTwoP segObj; rw [← hsX]; ring
      linarith
    obtain ⟨M, hM⟩ : ∃ M, M = max (valOne P) (valThree P) := ⟨_, rfl⟩
    rw [← hM] at hcond
    obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = valTwoP P X - M := ⟨_, rfl⟩
    have hΔ0 : 0 < Δ := by linarith
    set ε := min η (min (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m))) with hε
    have hε0 : 0 < ε := lt_min hη (lt_min (by linarith) (div_pos hΔ0 hL))
    obtain ⟨g2, ⟨hXg2, hg2ε⟩, hneg⟩ := hsign ε hε0
    have hε1 := min_le_left η (min (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m)))
    have hε2 := min_le_right η (min (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m)))
    have hε3 := min_le_left (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m))
    have hε4 := min_le_right (P.ξ - X) (Δ / ((P.ebar + P.eo) * P.m))
    have hg2η : g2 < X + η := by linarith
    have hg2ξ : g2 < P.ξ := by linarith
    have hval2 : M < valTwoP P g2 := by
      have hlo := hlow g2 (by linarith)
      have h1 : (g2 - X) * ((P.ebar + P.eo) * P.m) < Δ := by
        have : g2 - X < Δ / ((P.ebar + P.eo) * P.m) := by linarith
        rwa [lt_div_iff₀ hL] at this
      have h2 : (g2 - X) * (sX + P.eo) * aP P * P.m ≤ (g2 - X) * ((P.ebar + P.eo) * P.m) := by
        have h0 : 0 ≤ g2 - X := by linarith
        have h3 : 0 ≤ sX + P.eo := by linarith [hsXm.1]
        have : (sX + P.eo) * aP P ≤ (P.ebar + P.eo) * 1 :=
          mul_le_mul (by linarith [hsXm.2]) haP1.le haP0 (by linarith)
        have h4 : (sX + P.eo) * aP P * P.m ≤ (P.ebar + P.eo) * P.m := by
          have := mul_le_mul_of_nonneg_right this hm.le; linarith
        have h5 := mul_le_mul_of_nonneg_left h4 h0
        have h6 : (g2 - X) * (sX + P.eo) * aP P * P.m = (g2 - X) * ((sX + P.eo) * aP P * P.m) := by
          ring
        rw [h6]; exact h5
      linarith
    have hval1 : M < valTwoP P g1 := by
      have hlo := hlow g1 hg1.le
      have : 0 ≤ (X - g1) * (sX + P.eo) * aP P * P.m := by
        have : 0 ≤ X - g1 := by linarith
        have : 0 ≤ sX + P.eo := by linarith [hsXm.1]
        positivity
      linarith
    have hP1 : 0 < hP P g1 := hXmin g1 ⟨hg1.le, hg1X⟩
    unfold hP at hP1 hneg
    obtain ⟨-, hR1, -, -, hd1⟩ := caseP_reduction P hS hβc hv g1 hg1 (by linarith)
    obtain ⟨-, -, hR2, hd2, -⟩ := caseP_reduction P hS hβc hv g2 (by linarith) hg2ξ
    have hBR1 := hR1 (max_lt (by rw [← hM]; linarith) (by linarith))
    have hBR2 := hR2 (max_lt (by rw [← hM]; linarith) (by linarith))
    refine ⟨g1, g2, hg1, by linarith, ⟨_, _, _, (hBR1 _ _ _).2 ⟨rfl, rfl, rfl⟩⟩,
      ⟨_, _, _, (hBR2 _ _ _).2 ⟨rfl, rfl, rfl⟩⟩, ?_⟩
    intro p1 e1 t1 p2 e2 t2 h1 h2
    obtain ⟨rfl, rfl, rfl⟩ := (hBR1 _ _ _).1 h1
    obtain ⟨rfl, rfl, rfl⟩ := (hBR2 _ _ _).1 h2
    obtain ⟨hle, hstrict⟩ := hcmp g2 hXg2 hg2η
    have hKeo : (P.vh - P.vl) / P.ξ < P.eo := by
      rw [div_lt_iff₀ hξ]; linarith
    have hs1 : 0 ≤ segOpt P g1 1 :=
      (isSegOpt_segOpt' P hS g1 1 hg1.le zero_le_one le_rfl).1.1
    have hs2 : 0 ≤ segOpt P g2 (aP P) :=
      (isSegOpt_segOpt' P hS g2 (aP P) (by linarith) haP0 haP1.le).1.1
    refine ⟨by linarith, by linarith, hle, ?_, ?_, hstrict⟩
    · rw [hd1.1, hd2.1]
    · rw [hd1.2, hd2.2]
      have h8 : 0 < (1 - P.α) * P.m * (1 - P.βu) :=
        mul_pos (mul_pos (sub_pos.2 hα) hm) (sub_pos.2 hβu')
      have h7 : (1 - P.α) * P.βu * P.m = (1 - P.α) * P.m - (1 - P.α) * P.m * (1 - P.βu) := by ring
      rw [h7]; exact sub_lt_self _ h8
