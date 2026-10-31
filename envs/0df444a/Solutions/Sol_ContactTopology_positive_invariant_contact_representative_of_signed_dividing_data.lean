-- Prove2me | solution 1 for ContactTopology.positive_invariant_contact_representative_of_signed_dividing_data
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:15:01.478888+00:00
-- url     : https://prove2.me/submissions/8d42a02b-4f15-43ac-a9b2-560a152a806e

import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ContactTopology.DividedRepresentatives
open Set Function Filter
open scoped Topology ContDiff
noncomputable section

lemma uniform_crossing_collar {E : Type*} [TopologicalSpace E]
    (S : Set E) (hS : IsCompact S) (r g : E → ℝ) (hr : Continuous r) (hg : Continuous g)
    (hcross : ∀ x ∈ S, r x = 0 → g x < 0) :
    ∃ δ > 0, ∀ x ∈ S, |r x| ≤ δ → g x < 0 := by
  let B := S ∩ {x | 0 ≤ g x}
  have hB : IsCompact B := hS.inter_right (isClosed_le continuous_const hg)
  by_cases hne : B.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hB.exists_isMinOn hne (continuous_abs.comp hr).continuousOn
    have hrp : r p ≠ 0 := by
      intro hz
      exact (not_lt_of_ge hp.2) (hcross p hp.1 hz)
    refine ⟨|r p|/2,half_pos (abs_pos.mpr hrp),?_⟩
    intro x hx hsmall
    by_contra hn
    have hxb : x ∈ B := ⟨hx,le_of_not_gt hn⟩
    have hm := hmin hxb
    change |r p| ≤ |r x| at hm
    linarith [abs_pos.mpr hrp]
  · refine ⟨1,by norm_num,?_⟩
    intro x hx _
    by_contra hn
    exact hne ⟨x,hx,le_of_not_gt hn⟩

def clipBump (s : ℝ) : ℝ := expNegInvGlue (1-s^2)

lemma clipBump_smooth : ContDiff ℝ ∞ clipBump := by
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

lemma clipBump_nonneg (s : ℝ) : 0 ≤ clipBump s := expNegInvGlue.nonneg _

lemma clipBump_pos (s : ℝ) (hs : |s| < 1) : 0 < clipBump s := by
  apply expNegInvGlue.pos_of_pos
  have hh := (sq_lt_one_iff_abs_lt_one s).mpr hs
  linarith

lemma clipBump_zero (s : ℝ) (hs : 1 ≤ |s|) : clipBump s = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  have hh : 1 ≤ s^2 := by nlinarith [sq_abs s]
  linarith

def smoothClip (s : ℝ) : ℝ := ∫ t in (0:ℝ)..s, clipBump t

lemma smoothClip_hasDerivAt (s : ℝ) : HasDerivAt smoothClip (clipBump s) s := by
  have hc := clipBump_smooth.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma smoothClip_deriv (s : ℝ) : deriv smoothClip s = clipBump s :=
  (smoothClip_hasDerivAt s).deriv

lemma smoothClip_smooth : ContDiff ℝ ∞ smoothClip := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (smoothClip_hasDerivAt s).differentiableAt,?_⟩
  simpa only [funext smoothClip_deriv] using clipBump_smooth

lemma smoothClip_monotone : Monotone smoothClip :=
  monotone_of_deriv_nonneg (fun s => (smoothClip_hasDerivAt s).differentiableAt)
    (fun s => by rw [smoothClip_deriv]; exact clipBump_nonneg s)

lemma smoothClip_zero : smoothClip 0 = 0 := by simp [smoothClip]

lemma smoothClip_strict : StrictMonoOn smoothClip (Ioo (-1:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _) smoothClip_smooth.continuous.continuousOn
  intro s hs
  rw [interior_Ioo] at hs
  rw [smoothClip_deriv]
  exact clipBump_pos s (abs_lt.mpr hs)

lemma smoothClip_pos (s : ℝ) (hs : 0 < s) : 0 < smoothClip s := by
  let t := min s (1/2)
  have ht : 0 < t := lt_min hs (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hh := smoothClip_strict (by norm_num : (0:ℝ) ∈ Ioo (-1:ℝ) 1)
    (show t ∈ Ioo (-1:ℝ) 1 from ⟨by linarith,ht1⟩) ht
  rw [smoothClip_zero] at hh
  exact lt_of_lt_of_le hh (smoothClip_monotone (min_le_left _ _))

lemma smoothClip_neg (s : ℝ) (hs : s < 0) : smoothClip s < 0 := by
  let t := max s (-1/2)
  have ht : t < 0 := max_lt hs (by norm_num)
  have ht1 : -1 < t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hh := smoothClip_strict
    (show t ∈ Ioo (-1:ℝ) 1 from ⟨ht1,by linarith⟩)
    (by norm_num : (0:ℝ) ∈ Ioo (-1:ℝ) 1) ht
  rw [smoothClip_zero] at hh
  exact lt_of_le_of_lt (smoothClip_monotone (le_max_left _ _)) hh


/-- Construct the normal coefficient from signed divergence and transverse
crossing data. The contact inequality holds on a neighborhood of the compact set. -/
theorem positive_coefficient_from_divided_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : IsCompact S) (r : E → ℝ) (w : E → E) (h : E → ℝ)
    (hr : ContDiff ℝ ∞ r) (hw : ContDiff ℝ ∞ w) (hh : Continuous h)
    (hdiv : ∀ x ∈ S, r x ≠ 0 → 0 < r x*h x)
    (hcross : ∀ x ∈ S, r x = 0 → fderiv ℝ r x (w x) < 0) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ (∀ x, u x = 0 ↔ r x = 0) ∧
      (∀ x, r x ≠ 0 → 0 < u x*r x) ∧
      ∃ O : Set E, IsOpen O ∧ S ⊆ O ∧
        ∀ x ∈ O, 0 < u x*h x-fderiv ℝ u x (w x) := by
  let g : E → ℝ := fun x => fderiv ℝ r x (w x)
  have hg : ContDiff ℝ ∞ g := (hr.fderiv_right (by simp)).clm_apply hw
  obtain ⟨δ,hδ,hcollar⟩ := uniform_crossing_collar S hS r g hr.continuous hg.continuous hcross
  let u : E → ℝ := fun x => smoothClip (r x/δ)
  have hu : ContDiff ℝ ∞ u := smoothClip_smooth.comp (hr.div_const δ)
  have hdu : ∀ x, fderiv ℝ u x = (clipBump (r x/δ)/δ) • fderiv ℝ r x := by
    intro x
    have hd0 : HasFDerivAt (fun z => r z/δ) (δ⁻¹ • fderiv ℝ r x) x := by
      have heq : (fun z => r z/δ) = δ⁻¹ • r := by
        funext z
        simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
      rw [heq]
      exact (hr.differentiable (by simp) x).hasFDerivAt.const_smul δ⁻¹
    have hd := (smoothClip_hasDerivAt (r x/δ)).comp_hasFDerivAt x hd0
    change HasFDerivAt u _ x at hd
    rw [hd.fderiv]
    ext v
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hup : ∀ x, 0 < r x → 0 < u x := fun x hx => smoothClip_pos _ (div_pos hx hδ)
  have hun : ∀ x, r x < 0 → u x < 0 := fun x hx => smoothClip_neg _ (div_neg_of_neg_of_pos hx hδ)
  have huz : ∀ x, r x = 0 → u x = 0 := by
    intro x hx
    simp [u,hx,smoothClip_zero]
  have hsign : ∀ x, r x ≠ 0 → 0 < u x*r x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with hn | hp
    · exact mul_pos_of_neg_of_neg (hun x hn) hn
    · exact mul_pos (hup x hp) hp
  have hpositive : ∀ x ∈ S, 0 < u x*h x-fderiv ℝ u x (w x) := by
    intro x hx
    rw [hdu]
    change 0 < u x*h x-(clipBump (r x/δ)/δ)*g x
    by_cases hz : r x = 0
    · have hk : 0 < clipBump (r x/δ)/δ := by
        rw [hz,zero_div]
        exact div_pos (clipBump_pos 0 (by norm_num)) hδ
      have hc : g x < 0 := hcross x hx hz
      rw [huz x hz,zero_mul,zero_sub]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hk hc)
    · have hmain : 0 < u x*h x := by
        rcases (mul_pos_iff.mp (hdiv x hx hz)) with hp | hn
        · exact mul_pos (hup x hp.1) hp.2
        · exact mul_pos_of_neg_of_neg (hun x hn.1) hn.2
      have herror : (clipBump (r x/δ)/δ)*g x ≤ 0 := by
        by_cases hs : |r x/δ| < 1
        · have hsmall : |r x| ≤ δ := by
            rw [abs_div,abs_of_pos hδ] at hs
            exact le_of_lt ((div_lt_one hδ).mp hs)
          exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (clipBump_nonneg _) hδ.le)
            (hcollar x hx hsmall).le
        · rw [clipBump_zero _ (le_of_not_gt hs),zero_div,zero_mul]
      linarith
  let O := {x | 0 < u x*h x-fderiv ℝ u x (w x)}
  have hO : IsOpen O := isOpen_lt continuous_const
    ((hu.continuous.mul hh).sub (((hu.fderiv_right (by simp)).clm_apply hw).continuous))
  refine ⟨u,hu,?_,hsign,O,hO,hpositive,fun _ hx => hx⟩
  intro x
  constructor
  · intro hx
    by_contra hn
    have hp := hsign x hn
    rw [hx,zero_mul] at hp
    exact lt_irrefl 0 hp
  · exact huz x


theorem positive_invariant_representative
    (S : Set (Fin 2 → ℝ)) (hS : IsCompact S)
    (r : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hr : ContDiff ℝ ∞ r) (hβ : ContDiff ℝ ∞ β)
    (hdiv : ∀ x ∈ S, r x ≠ 0 →
      0 < r x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0))
    (hcross : ∀ x ∈ S, r x = 0 → fderiv ℝ r x ![β x 1,-β x 0] < 0) :
    ∃ u : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ u ∧ (∀ x, u x = 0 ↔ r x = 0) ∧
      (∀ x, r x ≠ 0 → 0 < u x*r x) ∧
      ∃ O : Set (Fin 2 → ℝ), IsOpen O ∧ S ⊆ O ∧
        ∀ x ∈ O, 0 < β x 0*fderiv ℝ u x (Pi.single 1 1)-
          β x 1*fderiv ℝ u x (Pi.single 0 1)+
          u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) := by
  let w : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => ![β x 1,-β x 0]
  let h : (Fin 2 → ℝ) → ℝ := fun x =>
    fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0
  have hw : ContDiff ℝ ∞ w := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [w] <;> fun_prop
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ β x) := hβ.fderiv_right (by simp)
  have hh : ContDiff ℝ ∞ h :=
    ((contDiff_apply ℝ ℝ 1).comp (hd.clm_apply contDiff_const)).sub
      ((contDiff_apply ℝ ℝ 0).comp (hd.clm_apply contDiff_const))
  obtain ⟨u,hu,hzero,hsign,O,hO,hSO,hpositive⟩ :=
    positive_coefficient_from_divided_data S hS r w h hr hw hh.continuous hdiv hcross
  refine ⟨u,hu,hzero,hsign,O,hO,hSO,?_⟩
  intro x hx
  have hp := hpositive x hx
  have he : w x = β x 1 • (Pi.single 0 1 : Fin 2 → ℝ)-β x 0 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [w]
  rw [he,map_sub,map_smul,map_smul] at hp
  dsimp only [h,smul_eq_mul] at hp
  linarith

end
end ContactTopology.DividedRepresentatives


open scoped ContDiff

theorem solution
    (S : Set (Fin 2 → ℝ)) (hS : IsCompact S)
    (r : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hr : ContDiff ℝ ∞ r) (hβ : ContDiff ℝ ∞ β)
    (hdiv : ∀ x ∈ S, r x ≠ 0 →
      0 < r x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0))
    (hcross : ∀ x ∈ S, r x = 0 → fderiv ℝ r x ![β x 1,-β x 0] < 0) :
    ∃ u : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ u ∧ (∀ x, u x = 0 ↔ r x = 0) ∧
      (∀ x, r x ≠ 0 → 0 < u x*r x) ∧
      ∃ O : Set (Fin 2 → ℝ), IsOpen O ∧ S ⊆ O ∧
        ∀ x ∈ O, 0 < β x 0*fderiv ℝ u x (Pi.single 1 1)-
          β x 1*fderiv ℝ u x (Pi.single 0 1)+
          u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) := by
  exact ContactTopology.DividedRepresentatives.positive_invariant_representative
    S hS r β hr hβ hdiv hcross
