-- Prove2me | solution 1 for ConvexOptAlg.CenterGravity.thm_2_1_volume_decay
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T20:01:02.236988+00:00
-- url     : https://prove2.me/submissions/5c7f9990-48ce-4e91-9966-5c7bd6c395c5

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs
import Theorems.Thm_ConvexOptAlg_CenterGravity_lemma_2_2

open MeasureTheory
open scoped InnerProductSpace

namespace CGAux

open ConvexOptAlg.CenterGravity

theorem inner_cut_neg {n : ℕ} (c x w : EuclideanSpace ℝ (Fin n)) :
    ⟪w, c - x⟫_ℝ = -⟪x - c, w⟫_ℝ := by
  rw [real_inner_comm, ← inner_neg_left]; congr 1; abel

theorem S_subset {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w) :
    ∀ s, 1 ≤ s → S s ⊆ X := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rw [hrun.init]
  | succ s hs ih => rw [hrun.cut s hs]; exact Set.inter_subset_left.trans ih

theorem removed_pos {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    (s : ℕ) (hs : 1 ≤ s) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S s) (hx' : x ∉ S (s + 1)) :
    0 < ⟪x - c s, w s⟫_ℝ := by
  rw [hrun.cut s hs] at hx'
  by_contra h
  exact hx' ⟨hx, not_lt.mp h⟩

theorem removed_gt {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    (s : ℕ) (hs : 1 ≤ s) {x : EuclideanSpace ℝ (Fin n)} (hxX : x ∈ X)
    (hpos : 0 < ⟪x - c s, w s⟫_ℝ) : f (c s) < f x := by
  have h := (hrun.oracle s hs).2 x hxX
  rw [inner_cut_neg] at h
  linarith

theorem xstar_mem {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) :
    ∀ t, 1 ≤ t → xstar ∈ S t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [hrun.init]; exact hxstar
  | succ t ht ih =>
    rw [hrun.cut t ht]
    refine ⟨ih, ?_⟩
    have h1 := (hrun.oracle t ht).2 xstar hxstar
    have h2 := hmin _ (hrun.oracle t ht).1
    rw [inner_cut_neg] at h1
    show ⟪xstar - c t, w t⟫_ℝ ≤ 0
    linarith

end CGAux
namespace CGAux

open ConvexOptAlg.CenterGravity

theorem body_vol {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    0 < volume K ∧ volume K < ⊤ :=
  ⟨lt_of_lt_of_le (isOpen_interior.measure_pos volume hK.2.2) (measure_mono interior_subset),
    hK.1.measure_lt_top⟩

theorem integral_self_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    ∫ x in K, x = (volume K).toReal • centroid K := by
  have h := body_vol hK
  have hne : (volume K).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h.1.ne', h.2.ne⟩
  unfold centroid
  rw [smul_inv_smul₀ hne]

theorem integral_centered {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    ∫ x in (fun y => y + centroid K) ⁻¹' K, x = 0 := by
  set c := centroid K with hc
  have hmeas : MeasurableSet K := hK.1.isClosed.measurableSet
  have hP : MeasurableSet ((fun y => y + c) ⁻¹' K) := hmeas.preimage (measurable_add_const c)
  have hint : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => y) K volume :=
    continuousOn_id.integrableOn_compact hK.1
  have hintc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => c) K volume :=
    continuousOn_const.integrableOn_compact hK.1
  have e1 : ∫ x in (fun y => y + c) ⁻¹' K, x =
      ∫ x, K.indicator (fun y => y - c) (x + c) := by
    rw [← integral_indicator hP]
    congr 1
    funext x
    by_cases hx : x + c ∈ K
    · have : x ∈ (fun y => y + c) ⁻¹' K := hx
      simp [Set.indicator, this, hx]
    · have : x ∉ (fun y => y + c) ⁻¹' K := hx
      simp [Set.indicator, this, hx]
  rw [e1, integral_add_right_eq_self (fun y => K.indicator (fun y => y - c) y) c,
    integral_indicator hmeas, integral_sub hint hintc, setIntegral_const, integral_self_eq hK]
  simp [Measure.real, ← hc]

end CGAux
namespace CGAux

open ConvexOptAlg.CenterGravity

theorem body_translate {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (c : EuclideanSpace ℝ (Fin n)) : IsConvexBody ((fun y => y + c) ⁻¹' K) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Homeomorph.addRight c).isCompact_preimage.mpr hK.1
  · exact hK.2.1.translate_preimage_left c
  · have : (fun y => y + c) ⁻¹' interior K ⊆ interior ((fun y => y + c) ⁻¹' K) := by
      rw [show (fun y : EuclideanSpace ℝ (Fin n) => y + c) = ⇑(Homeomorph.addRight c) from rfl,
        Homeomorph.preimage_interior]
    obtain ⟨x, hx⟩ := hK.2.2
    exact ⟨x - c, this (by simpa using hx)⟩

theorem grunbaum_shift {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) :
    ENNReal.ofReal (Real.exp (-1)) * volume K ≤
      volume (K ∩ {x | 0 ≤ ⟪x - centroid K, w⟫_ℝ}) := by
  set c := centroid K
  have h := lemma_2_2 ((fun y => y + c) ⁻¹' K) (body_translate hK c) (integral_centered hK) w hw
  have e2 : (fun y => y + c) ⁻¹' K ∩ {x | 0 ≤ ⟪x, w⟫_ℝ} =
      (fun y => y + c) ⁻¹' (K ∩ {x | 0 ≤ ⟪x - c, w⟫_ℝ}) := by
    ext y; simp
  rw [measure_preimage_add_right, e2, measure_preimage_add_right] at h
  exact h

theorem hyperplane_null {n : ℕ} (c w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) :
    volume {x : EuclideanSpace ℝ (Fin n) | ⟪x - c, w⟫_ℝ = 0} = 0 := by
  have hker : (ℝ ∙ w)ᗮ ≠ ⊤ := by
    rw [Ne, Submodule.orthogonal_eq_top_iff, Submodule.span_singleton_eq_bot]
    exact hw
  have e : {x : EuclideanSpace ℝ (Fin n) | ⟪x - c, w⟫_ℝ = 0} =
      (fun x => x + (-c)) ⁻¹' ((ℝ ∙ w)ᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_right, ← sub_eq_add_neg]
    rw [real_inner_comm]
  rw [e, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ hker

theorem halfspace_convex {n : ℕ} (c w : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ⟪x - c, w⟫_ℝ ≤ 0} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    have : c = (a + b) • c := by rw [hab, one_smul]
    conv_lhs => rw [this]
    module
  rw [this, inner_add_left, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  nlinarith

theorem step {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) :
    IsConvexBody (K ∩ {x | ⟪x - centroid K, w⟫_ℝ ≤ 0}) ∧
    volume (K ∩ {x | ⟪x - centroid K, w⟫_ℝ ≤ 0}) ≤
      ENNReal.ofReal (1 - Real.exp (-1)) * volume K := by
  set c := centroid K with hc
  set H : Set (EuclideanSpace ℝ (Fin n)) := {x | ⟪x - c, w⟫_ℝ ≤ 0} with hH
  have hHc : IsClosed H := isClosed_le (by fun_prop) continuous_const
  have hHm : MeasurableSet H := hHc.measurableSet
  have hV := body_vol hK
  have hlow : ENNReal.ofReal (Real.exp (-1)) * volume K ≤ volume (K ∩ H) := by
    have := grunbaum_shift hK (-w) (neg_ne_zero.mpr hw)
    have e : {x : EuclideanSpace ℝ (Fin n) | 0 ≤ ⟪x - centroid K, -w⟫_ℝ} = H := by
      ext x; simp [hH, hc, inner_neg_right]
    rwa [e] at this
  have hpos : 0 < volume (K ∩ H) := by
    refine lt_of_lt_of_le ?_ hlow
    exact ENNReal.mul_pos (by simp [ENNReal.ofReal_pos, Real.exp_pos]) hV.1.ne'
  refine ⟨⟨hK.1.inter_right hHc, hK.2.1.inter (halfspace_convex c w), ?_⟩, ?_⟩
  · by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hcl : IsClosed (K ∩ H) := hK.1.isClosed.inter hHc
    have hconv : Convex ℝ (K ∩ H) := hK.2.1.inter (halfspace_convex c w)
    have hsub : K ∩ H ⊆ frontier (K ∩ H) := by
      intro x hx
      have : x ∈ closure (K ∩ H) := subset_closure hx
      rw [closure_eq_interior_union_frontier, hne] at this
      simpa using this
    have := hconv.addHaar_frontier volume
    have := measure_mono_null hsub this
    exact hpos.ne' this
  · have hsplit := measure_inter_add_diff (μ := volume) K hHm
    have hR : ENNReal.ofReal (Real.exp (-1)) * volume K ≤ volume (K \ H) := by
      have := grunbaum_shift hK w hw
      refine this.trans ?_
      have hsub : K ∩ {x | 0 ≤ ⟪x - centroid K, w⟫_ℝ} ⊆
          (K \ H) ∪ {x | ⟪x - c, w⟫_ℝ = 0} := by
        intro x hx
        by_cases h0 : ⟪x - c, w⟫_ℝ = 0
        · exact Or.inr h0
        · left
          refine ⟨hx.1, fun hxH => h0 ?_⟩
          exact le_antisymm hxH hx.2
      calc _ ≤ volume ((K \ H) ∪ {x | ⟪x - c, w⟫_ℝ = 0}) := measure_mono hsub
        _ ≤ volume (K \ H) + volume {x | ⟪x - c, w⟫_ℝ = 0} := measure_union_le _ _
        _ = volume (K \ H) := by rw [hyperplane_null c w hw, add_zero]
    have hlt : Real.exp (-1) < 1 := by simpa using Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
    have hsum : ENNReal.ofReal (1 - Real.exp (-1)) * volume K +
        ENNReal.ofReal (Real.exp (-1)) * volume K = volume K := by
      rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (Real.exp_pos _).le]
      simp
    have hfin : ENNReal.ofReal (Real.exp (-1)) * volume K ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV.2.ne
    refine (ENNReal.add_le_add_iff_right hfin).mp ?_
    rw [hsum]
    calc volume (K ∩ H) + ENNReal.ofReal (Real.exp (-1)) * volume K
        ≤ volume (K ∩ H) + volume (K \ H) := by gcongr
      _ = volume K := hsplit

end CGAux

theorem solution {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : ConvexOptAlg.CenterGravity.IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {S : ℕ → Set (EuclideanSpace ℝ (Fin n))} {c w : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : ConvexOptAlg.CenterGravity.IsCenterOfGravityRun X f S c w) (t : ℕ)
    (hw : ∀ s : ℕ, 1 ≤ s → s ≤ t → w s ≠ 0) :
    volume (S (t + 1)) ≤ ENNReal.ofReal ((1 - Real.exp (-1)) ^ t) * volume X := by
  have hlt : Real.exp (-1) < 1 := by
    simpa using Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
  have key : ∀ s, 1 ≤ s → s ≤ t + 1 →
      ConvexOptAlg.CenterGravity.IsConvexBody (S s) ∧
      volume (S s) ≤ ENNReal.ofReal ((1 - Real.exp (-1)) ^ (s - 1)) * volume X := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => intro _; rw [hrun.init]; simp; exact hX
    | succ s hs ih =>
      intro hst
      obtain ⟨hb, hv⟩ := ih (by omega)
      obtain ⟨hb', hv'⟩ := CGAux.step hb (w s) (hw s hs (by omega))
      rw [hrun.cut s hs, hrun.center s hs]
      refine ⟨hb', ?_⟩
      have e : s + 1 - 1 = (s - 1) + 1 := by omega
      rw [e, pow_succ', ENNReal.ofReal_mul (by linarith), mul_assoc]
      exact hv'.trans (by gcongr)
  simpa using (key (t + 1) (by omega) le_rfl).2
