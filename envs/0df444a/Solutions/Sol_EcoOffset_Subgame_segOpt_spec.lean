-- Prove2me | solution 1 for EcoOffset.Subgame.segOpt_spec
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:18:53.505504+00:00
-- url     : https://prove2.me/submissions/4b5988a7-e109-414b-a444-1e0fabb570e2

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoSegAux
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

theorem isSegOpt_unique (P : Params) (hS : P.Standing) (x a : ℝ) (ha : 0 ≤ a) {e1 e2 : ℝ}
    (h1 : IsSegOpt P x a e1) (h2 : IsSegOpt P x a e2) : e1 = e2 := by
  have key : ∀ {u v : ℝ}, IsSegOpt P x a u → IsSegOpt P x a v → ¬ u < v := by
    intro u v hu hv huv
    obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = (u + v) / 2 := ⟨_, rfl⟩
    have hw : w ∈ Set.Icc 0 P.ebar := ⟨by linarith [hu.1.1], by linarith [hv.1.2]⟩
    rcases le_total 0 (Dseg P x a w) with hD | hD
    · have := segObj_lt_of_Dseg_nonneg P hS x a ha hu.1 hw (by linarith) hD
      linarith [hu.2 w hw]
    · have := segObj_lt_of_Dseg_nonpos P hS x a ha hw hv.1 (by linarith) hD
      linarith [hv.2 w hw]
  rcases lt_trichotomy e1 e2 with h | h | h
  · exact absurd h (key h1 h2)
  · exact h
  · exact absurd h (key h2 h1)

theorem exists_isSegOpt (P : Params) (hS : P.Standing) (x a : ℝ) : ∃ e, IsSegOpt P x a e := by
  have heb : 0 ≤ P.ebar := hS.2.1.le
  obtain ⟨e, he, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 heb)
    (continuous_segObj P hS x a).continuousOn
  exact ⟨e, he, fun e' he' => (isMaxOn_iff.1 hmax) e' he'⟩

theorem isSegOpt_segOpt (P : Params) (hS : P.Standing) (x a : ℝ) :
    IsSegOpt P x a (segOpt P x a) := by
  have h := exists_isSegOpt P hS x a
  unfold segOpt
  rw [dif_pos h]
  exact h.choose_spec

theorem le_segOpt (P : Params) (hS : P.Standing) (x a : ℝ) (ha : 0 ≤ a) {e : ℝ}
    (he : e ∈ Set.Icc 0 P.ebar) (hD : 0 ≤ Dseg P x a e) : e ≤ segOpt P x a := by
  have hs := isSegOpt_segOpt P hS x a
  by_contra hlt
  push Not at hlt
  have := segObj_lt_of_Dseg_nonneg P hS x a ha hs.1 he hlt hD
  linarith [hs.2 e he]

theorem segOpt_le (P : Params) (hS : P.Standing) (x a : ℝ) (ha : 0 ≤ a) {e : ℝ}
    (he : e ∈ Set.Icc 0 P.ebar) (hD : Dseg P x a e ≤ 0) : segOpt P x a ≤ e := by
  have hs := isSegOpt_segOpt P hS x a
  by_contra hlt
  push Not at hlt
  have := segObj_lt_of_Dseg_nonpos P hS x a ha he hs.1 hlt hD
  linarith [hs.2 e he]

end EcoSegAux

open EcoOffset.Subgame in
theorem solution (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsSegOpt P x a (segOpt P x a) ∧
    (∀ e, IsSegOpt P x a e → e = segOpt P x a) ∧
    (∀ e ∈ Set.Icc 0 P.ebar,
      (x + deriv P.c e) * a * P.m + deriv P.f e = 0 → segOpt P x a = e) ∧
    segOpt P 0 a = P.ebar := by
  have hs := EcoSegAux.isSegOpt_segOpt P hS x a
  refine ⟨hs, fun e he => EcoSegAux.isSegOpt_unique P hS x a ha0 he hs, ?_, ?_⟩
  · intro e he hfoc
    have hD : EcoSegAux.Dseg P x a e = 0 := by
      unfold EcoSegAux.Dseg; linarith
    have hopt : IsSegOpt P x a e := by
      refine ⟨he, fun e' he' => ?_⟩
      rcases lt_trichotomy e' e with h | h | h
      · exact (EcoSegAux.segObj_lt_of_Dseg_nonneg P hS x a ha0 he' he h hD.ge).le
      · rw [h]
      · exact (EcoSegAux.segObj_lt_of_Dseg_nonpos P hS x a ha0 he he' h hD.le).le
    exact EcoSegAux.isSegOpt_unique P hS x a ha0 hs hopt
  · have hS' := hS
    obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
      hder⟩ := hS'
    have hebar : P.ebar ∈ Set.Icc 0 P.ebar := ⟨heb.le, le_rfl⟩
    apply le_antisymm (EcoSegAux.isSegOpt_segOpt P hS 0 a).1.2
    apply EcoSegAux.le_segOpt P hS 0 a ha0 hebar
    obtain ⟨h1, -, h3, -⟩ := hder P.ebar hebar
    unfold EcoSegAux.Dseg
    have : 0 ≤ -(deriv P.c P.ebar + 0) * a * P.m := by
      have : 0 ≤ -(deriv P.c P.ebar + 0) := by linarith
      positivity
    linarith
