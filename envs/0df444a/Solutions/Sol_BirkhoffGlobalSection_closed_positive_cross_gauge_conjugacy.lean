-- Prove2me | solution 1 for BirkhoffGlobalSection.closed_positive_cross_gauge_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:31:16.224874+00:00
-- url     : https://prove2.me/submissions/95b889fa-fe85-44fe-9456-8ae6266a999d

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic

namespace BirkhoffGlobalSection.AngularLift
open Complex

noncomputable def unit (u : ℝ) : ℂ := Complex.exp ((u : ℂ) * Complex.I)

lemma unit_ne_zero (u : ℝ) : unit u ≠ 0 := Complex.exp_ne_zero _
lemma unit_norm (u : ℝ) : ‖unit u‖ = 1 := by simp [unit, Complex.norm_exp]
lemma unit_mul_star (u : ℝ) : unit u * star (unit u) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, unit_norm]
  norm_num
lemma unit_continuous : Continuous unit := by unfold unit; fun_prop
lemma unit_period (u : ℝ) : unit (u + 2 * Real.pi) = unit u := by
  simp [unit, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I]

noncomputable def angle (A : ℂ →L[ℝ] ℂ) (u : ℝ) : ℝ :=
  u + Complex.arg (star (unit u) * A (unit u))

lemma angle_offset_bounds (A : ℂ →L[ℝ] ℂ)
    (hA : ∀ z : ℂ, z ≠ 0 → 0 < (star z * A z).im) (u : ℝ) :
    0 < angle A u - u ∧ angle A u - u < Real.pi := by
  have hi := hA (unit u) (unit_ne_zero u)
  have hnonneg : 0 ≤ Complex.arg (star (unit u) * A (unit u)) :=
    Complex.arg_nonneg_iff.mpr hi.le
  have hne : Complex.arg (star (unit u) * A (unit u)) ≠ 0 := by
    intro he
    have him := (Complex.arg_eq_zero_iff.mp he).2
    linarith
  have hpos : 0 < Complex.arg (star (unit u) * A (unit u)) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hlt : Complex.arg (star (unit u) * A (unit u)) < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')
  simpa [angle] using And.intro hpos hlt

lemma angle_continuous (A : ℂ →L[ℝ] ℂ)
    (hA : ∀ z : ℂ, z ≠ 0 → 0 < (star z * A z).im) : Continuous (angle A) := by
  have hf : Continuous fun u => star (unit u) * A (unit u) :=
    unit_continuous.star.mul (A.continuous.comp unit_continuous)
  have harg : Continuous fun u => Complex.arg (star (unit u) * A (unit u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr
      (Or.inr (hA (unit u) (unit_ne_zero u)).ne'))).comp (f := fun v => star (unit v) * A (unit v)) (hf.continuousAt)
  exact continuous_id.add harg

lemma angle_period (A : ℂ →L[ℝ] ℂ) (u : ℝ) :
    angle A (u + 2 * Real.pi) = angle A u + 2 * Real.pi := by
  simp only [angle, unit_period]
  ring

lemma angle_polar (A : ℂ →L[ℝ] ℂ) (u : ℝ) :
    A (unit u) = (‖A (unit u)‖ : ℂ) * unit (angle A u) := by
  have hn : ‖star (unit u) * A (unit u)‖ = ‖A (unit u)‖ := by
    simp [norm_mul, unit_norm]
  calc A (unit u) = unit u * (star (unit u) * A (unit u)) := by
         rw [← mul_assoc, unit_mul_star, one_mul]
       _ = unit u * ((‖A (unit u)‖ : ℂ) *
           Complex.exp ((Complex.arg (star (unit u) * A (unit u)) : ℂ) * Complex.I)) := by
         rw [← hn, Complex.norm_mul_exp_arg_mul_I]
       _ = (‖A (unit u)‖ : ℂ) * unit (angle A u) := by
         simp only [unit, angle, Complex.ofReal_add, add_mul, Complex.exp_add]
         ring

lemma injective_of_positive_cross (A : ℂ →L[ℝ] ℂ)
    (hA : ∀ z : ℂ, z ≠ 0 → 0 < (star z * A z).im) : Function.Injective A := by
  intro z w he
  apply sub_eq_zero.mp
  by_contra hn
  have hp := hA (z - w) hn
  have hz : A (z - w) = 0 := by rw [map_sub, he, sub_self]
  rw [hz, mul_zero, zero_im] at hp
  linarith

lemma angle_injective (A : ℂ →L[ℝ] ℂ)
    (hA : ∀ z : ℂ, z ≠ 0 → 0 < (star z * A z).im) : Function.Injective (angle A) := by
  intro u v he
  have hAi := injective_of_positive_cross A hA
  have hnu : 0 < ‖A (unit u)‖ := norm_pos_iff.mpr (by
    intro hz; have hp := hA (unit u) (unit_ne_zero u); rw [hz, mul_zero, zero_im] at hp; linarith)
  have hnv : 0 < ‖A (unit v)‖ := norm_pos_iff.mpr (by
    intro hz; have hp := hA (unit v) (unit_ne_zero v); rw [hz, mul_zero, zero_im] at hp; linarith)
  have hscaled : A (‖A (unit v)‖ • unit u) = A (‖A (unit u)‖ • unit v) := by
    rw [map_smul, map_smul]
    calc ‖A (unit v)‖ • A (unit u)
        = ‖A (unit v)‖ • ((‖A (unit u)‖ : ℂ) * unit (angle A u)) :=
          congrArg (fun w : ℂ => ‖A (unit v)‖ • w) (angle_polar A u)
      _ = ‖A (unit u)‖ • ((‖A (unit v)‖ : ℂ) * unit (angle A v)) := by
          rw [he]; simp only [Complex.real_smul]; ring
      _ = ‖A (unit u)‖ • A (unit v) :=
          congrArg (fun w : ℂ => ‖A (unit u)‖ • w) (angle_polar A v).symm
  have hscaled' := hAi hscaled
  have hn := congrArg norm hscaled'
  have hnormeq : ‖A (unit v)‖ = ‖A (unit u)‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hnu, abs_of_pos hnv,
      unit_norm, mul_one] using hn
  have huv : unit u = unit v := by
    rw [hnormeq] at hscaled'
    exact (smul_right_injective ℂ hnu.ne') hscaled'
  have hu := angle_offset_bounds A hA u
  have hv := angle_offset_bounds A hA v
  have hlow : -Real.pi < u - v := by linarith
  have hhi : u - v ≤ Real.pi := by linarith
  have hexp : Complex.exp (((u - v : ℝ) : ℂ) * Complex.I) = Complex.exp 0 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.exp_zero]
    change unit u / unit v = 1
    rw [huv, div_self (unit_ne_zero v)]
  have hzero := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := ((u - v : ℝ) : ℂ) * Complex.I) (y := 0)
    (by simpa using hlow) (by simpa using hhi)
    (by simpa using Real.pi_pos) (by simp [Real.pi_nonneg]) hexp
  have him := congrArg Complex.im hzero
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero, Complex.zero_im] at him
  linarith

lemma angle_strictMono (A : ℂ →L[ℝ] ℂ)
    (hA : ∀ z : ℂ, z ≠ 0 → 0 < (star z * A z).im) : StrictMono (angle A) := by
  obtain h | h := (angle_continuous A hA).strictMono_of_inj (angle_injective A hA)
  · exact h
  · have he := h Real.two_pi_pos
    have hp := angle_period A 0
    simp only [zero_add] at hp
    linarith [Real.pi_pos]

end BirkhoffGlobalSection.AngularLift

namespace BirkhoffGlobalSection.AngularLift
open Complex

lemma unit_eq_of_pos_scaled {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : (a : ℂ) * unit u = (b : ℂ) * unit v) : unit u = unit v := by
  have hn := congrArg norm h
  have hab : a = b := by simpa only [norm_mul, unit_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb] using hn
  rw [← hab] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne') h

/-- Covering-space lift for an arbitrary continuous nonzero complex path.
Adapted from Mazecto's exists_polarC_lift, accepted submission
893234ef-5ec2-4f4b-b415-f79ec1030002, with arbitrary initial phase. -/
lemma nonzero_path_angle_lift (w : ℝ → ℂ)
    (hw : ContinuousOn w (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≠ 0) :
    ∃ (s : ℝ) (β : ℝ → ℝ), s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
      Continuous β ∧ β 0 = s ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ w t = (r : ℂ) * unit (β t) := by
  have hw0 := hne 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨k, hk, -⟩ := existsUnique_add_zsmul_mem_Ico Real.two_pi_pos (Complex.arg (w 0)) 0
  let s := Complex.arg (w 0) + k • (2 * Real.pi)
  have hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by simpa only [zero_add] using hk
  have hup : unit s = unit (Complex.arg (w 0)) :=
    Function.Periodic.zsmul unit_period k _
  let σ : ℂ := (Real.log ‖w 0‖ : ℂ) + (s : ℂ) * Complex.I
  have hσ : Complex.exp σ = w 0 := by
    simp only [σ, Complex.exp_add, ← Complex.ofReal_exp]
    rw [Real.exp_log (norm_pos_iff.mpr hw0)]
    change (‖w 0‖ : ℂ) * unit s = w 0
    rw [hup]
    exact Complex.norm_mul_exp_arg_mul_I _
  let γ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨w t, hne t t.2⟩, hw.restrict.subtype_mk _⟩
  have γ0 : γ 0 = (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) σ := by
    apply Subtype.ext
    exact hσ.symm
  obtain ⟨Γ, hΓ, hΓ0⟩ := Complex.isCoveringMap_exp.exists_path_lifts γ σ γ0
  refine ⟨s, fun t => (Γ (Set.projIcc 0 1 zero_le_one t)).im, hs,
    (continuous_im.comp Γ.continuous).comp continuous_projIcc, ?_, ?_⟩
  · change (Γ (Set.projIcc 0 1 zero_le_one 0)).im = s
    rw [Set.projIcc_left]
    have he : (⟨0, Set.left_mem_Icc.mpr zero_le_one⟩ : Set.Icc (0 : ℝ) 1) =
        (0 : unitInterval) := rfl
    rw [he, hΓ0]
    simp [σ]
  · intro t ht
    have he : Complex.exp (Γ ⟨t, ht⟩) = w t := congrArg Subtype.val (congrFun hΓ ⟨t, ht⟩)
    refine ⟨Real.exp (Γ ⟨t, ht⟩).re, Real.exp_pos _, ?_⟩
    change w t = (Real.exp (Γ ⟨t, ht⟩).re : ℂ) *
      unit (Γ (Set.projIcc 0 1 zero_le_one t)).im
    rw [Set.projIcc_of_mem _ ht, ← he]
    conv_lhs => rw [← Complex.re_add_im (Γ ⟨t, ht⟩)]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    rfl

lemma angle_difference_constant (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1))
    (he : ∀ t ∈ Set.Icc (0 : ℝ) 1, unit (f t) = unit (g t)) :
    f 1 - g 1 = f 0 - g 0 := by
  let d : unitInterval → ℂ := fun t => ((f t - g t : ℝ) : ℂ) * Complex.I
  have hd : Continuous d :=
    (Complex.continuous_ofReal.comp (hf.sub hg).restrict).mul continuous_const
  have hExp : ∀ t : unitInterval, Complex.exp (d t) = 1 := by
    intro t
    simp only [d, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    change unit (f t) / unit (g t) = 1
    rw [he t t.2, div_self (unit_ne_zero _)]
  have hconst := Complex.isCoveringMap_exp.const_of_comp hd (fun t s => by
    apply Subtype.ext
    exact (hExp t).trans (hExp s).symm) (1 : unitInterval) (0 : unitInterval)
  have him := congrArg Complex.im hconst
  simpa [d] using him

/-- A closed family of positive-cross-product linear changes of coordinates
preserves endpoint winding through one fixed increasing angular conjugacy. -/
lemma closed_gauge_conjugacy (A : ℝ → (ℂ →L[ℝ] ℂ))
    (hAc : ContinuousOn A (Set.Icc 0 1)) (hAend : A 1 = A 0)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, z ≠ 0 → 0 < (star z * A t z).im)
    (w : ℝ → ℂ) (hw : ContinuousOn w (Set.Icc 0 1))
    (hwne : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≠ 0)
    (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1))
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ ρ : ℝ, 0 < ρ ∧ A t (w t) = (ρ : ℂ) * unit (θ t)) :
    ∃ (s : ℝ) (β a : ℝ → ℝ),
      s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧ Continuous β ∧ β 0 = s ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ w t = (r : ℂ) * unit (β t)) ∧
      StrictMono a ∧ (∀ u : ℝ, a (u + 2 * Real.pi) = a u + 2 * Real.pi) ∧
      θ 1 - θ 0 = a (β 1) - a s := by
  obtain ⟨s, β, hs, hβc, hβ0, hβ⟩ := nonzero_path_angle_lift w hw hwne
  let g : ℝ → ℝ := fun t => angle (A t) (β t)
  have hgc : ContinuousOn g (Set.Icc 0 1) := by
    have hu : ContinuousOn (fun t => unit (β t)) (Set.Icc 0 1) :=
      (unit_continuous.comp hβc).continuousOn
    have hf : ContinuousOn (fun t => star (unit (β t)) * A t (unit (β t))) (Set.Icc 0 1) :=
      hu.star.mul (hAc.clm_apply hu)
    apply hβc.continuousOn.add
    intro t ht
    exact (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr
      (Or.inr (hA t ht (unit (β t)) (unit_ne_zero _)).ne'))).comp_continuousWithinAt
        (f := fun v => star (unit (β v)) * A v (unit (β v))) (hf t ht)
  have hunit : ∀ t ∈ Set.Icc (0 : ℝ) 1, unit (θ t) = unit (g t) := by
    intro t ht
    obtain ⟨r, hr, hwr⟩ := hβ t ht
    obtain ⟨ρ, hρ, hθt⟩ := hθ t ht
    have hn : 0 < ‖A t (unit (β t))‖ := norm_pos_iff.mpr (by
      intro hz
      have hp := hA t ht (unit (β t)) (unit_ne_zero _)
      rw [hz, mul_zero, zero_im] at hp
      linarith)
    apply unit_eq_of_pos_scaled hρ (mul_pos hr hn)
    calc (ρ : ℂ) * unit (θ t) = A t (w t) := hθt.symm
      _ = (r : ℂ) * A t (unit (β t)) := by
        rw [hwr, ← Complex.real_smul, map_smul, Complex.real_smul]
      _ = (r : ℂ) * ((‖A t (unit (β t))‖ : ℂ) * unit (g t)) :=
        congrArg (fun z : ℂ => (r : ℂ) * z) (angle_polar (A t) (β t))
      _ = ((r * ‖A t (unit (β t))‖ : ℝ) : ℂ) * unit (g t) := by
        rw [Complex.ofReal_mul, mul_assoc]
  have he := angle_difference_constant θ g hθc hgc hunit
  refine ⟨s, β, angle (A 0), hs, hβc, hβ0, hβ,
    angle_strictMono (A 0) (hA 0 ⟨le_rfl, zero_le_one⟩), angle_period (A 0), ?_⟩
  dsimp [g] at he
  rw [hAend, hβ0] at he
  linarith

end BirkhoffGlobalSection.AngularLift

theorem solution (A : ℝ → (ℂ →L[ℝ] ℂ))
    (hAc : ContinuousOn A (Set.Icc 0 1)) (hAend : A 1 = A 0)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, z ≠ 0 → 0 < (star z * A t z).im)
    (w : ℝ → ℂ) (hw : ContinuousOn w (Set.Icc 0 1))
    (hwne : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≠ 0)
    (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1))
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ ρ : ℝ, 0 < ρ ∧ A t (w t) = (ρ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) :
    ∃ (s : ℝ) (β a : ℝ → ℝ),
      s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧ Continuous β ∧ β 0 = s ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ w t = (r : ℂ) * Complex.exp ((β t : ℂ) * Complex.I)) ∧
      StrictMono a ∧ (∀ u : ℝ, a (u + 2 * Real.pi) = a u + 2 * Real.pi) ∧
      θ 1 - θ 0 = a (β 1) - a s := by
  simpa only [BirkhoffGlobalSection.AngularLift.unit] using
    BirkhoffGlobalSection.AngularLift.closed_gauge_conjugacy A hAc hAend hA w hw hwne θ hθc hθ
