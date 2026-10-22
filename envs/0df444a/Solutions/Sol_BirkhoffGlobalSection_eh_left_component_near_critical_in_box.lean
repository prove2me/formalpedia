-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_component_near_critical_in_box
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:00:10.874694+00:00
-- url     : https://prove2.me/submissions/cd571c21-9c52-4f67-b0f8-f4f40657feff

import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_forbidden
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_regular
import Definitions.Def_BirkhoffGlobalSection_EHRegularization_Map
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Assembly of the elliptic-hyperbolic regularization model. -/

namespace BirkhoffGlobalSection

namespace EHReg

open Complex EHArsinh

noncomputable section

theorem position_radius_eq (μ : ℝ) (s : Phase) :
    ((leviCivitaPosition μ s) 0 + μ) ^ 2 + ((leviCivitaPosition μ s) 1) ^ 2 =
      (2 * zNormSq s) ^ 2 := by
  simp [leviCivitaPosition, zNormSq]; ring

theorem component_subset_source {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) : leftEnergyComponent μ c ⊆ sourceEH := by
  obtain ⟨ρ, hρ, h⟩ := left_component_position_radius_lt_one μ c hμ0 hμ1 hc
  intro s hs
  have h1 := h s hs
  rw [position_radius_eq] at h1
  have h0 : 0 ≤ 2 * zNormSq s := by unfold zNormSq; positivity
  show 2 * zNormSq s < 1
  nlinarith

theorem mem_locus_of_component {μ c : ℝ} {s : Phase} (hs : s ∈ leftEnergyComponent μ c) :
    s ∈ regularEnergyLocus μ c := connectedComponentIn_subset _ _ hs

theorem G_zero_of_mem {μ c : ℝ} {t : Phase} (ht : t ∈ ehLeftEnergyComponent μ c) :
    ehLeftHamiltonian μ c t = 0 := by
  unfold ehLeftEnergyComponent at ht
  have h := connectedComponentIn_subset _ _ ht
  exact h

theorem two_zNormSq_fromEH (μ : ℝ) (t : Phase) :
    2 * zNormSq (fromEH μ t) = normSq (sinh (zC t / 2)) := by
  have hz : zNormSq (fromEH μ t) = normSq (zC (fromEH μ t)) := by
    simp [zNormSq, normSq_apply, zC, fromEH, ofC]; ring
  rw [hz, fromEH, zC_ofC, normSq_div, normSq_mul, normSq_I, normSq_ofReal,
    Real.mul_self_sqrt (by norm_num)]
  ring

/-- A zero of `G` in the target comes from a zero of `K` in the regular locus. -/
theorem fromEH_mem_locus {μ c : ℝ} {t : Phase} (ht : t ∈ targetEH)
    (hG : ehLeftHamiltonian μ c t = 0) : fromEH μ t ∈ regularEnergyLocus μ c := by
  have hs := fromEH_mem_source μ ht
  have hK := G_toEH μ c hs
  rw [toEH_fromEH μ ht, hG] at hK
  have hD := secondCollisionDistanceSq_pos hs
  have hq := Real.sqrt_pos.2 hD
  refine ⟨?_, hD⟩
  rcases mul_eq_zero.1 hK.symm with h | h
  · linarith
  · exact h

theorem image_subset_eh {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    toEH μ '' leftEnergyComponent μ c ⊆ ehLeftEnergyComponent μ c := by
  have hsub := component_subset_source hμ0 hμ1 hc
  apply IsPreconnected.subset_connectedComponentIn
  · exact isPreconnected_connectedComponentIn.image _
      ((contDiffOn_toEH μ (n := 0)).continuousOn.mono hsub)
  · exact ⟨leftCollisionPoint μ, leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1,
      toEH_leftCollisionPoint hμ1⟩
  · rintro _ ⟨s, hs, rfl⟩
    show ehLeftHamiltonian μ c (toEH μ s) = 0
    rw [G_toEH μ c (hsub hs), (mem_locus_of_component hs).1, mul_zero]

/-- The EH component stays inside the target (barrier at a forbidden circle). -/
theorem eh_subset_target {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) : ehLeftEnergyComponent μ c ⊆ targetEH := by
  obtain ⟨r, hr0, hr1, hcirc⟩ := inner_lagrange_subcritical_circle_forbidden μ c hμ0 hμ1 hc
  set ν : Phase → ℝ := fun t => normSq (sinh (zC t / 2)) with hν
  have hνc : Continuous ν :=
    Complex.continuous_normSq.comp (Complex.continuous_sinh.comp (continuous_zC.div_const 2))
  have himc : Continuous fun t : Phase => |(zC t).im| :=
    (continuous_abs.comp Complex.continuous_im).comp continuous_zC
  set Ua : Set Phase := {t | ν t < r ∧ |(zC t).im| < Real.pi}
  set Ub : Set Phase := {t | r < ν t} ∪ {t | Real.pi < |(zC t).im|}
  have hUa : IsOpen Ua := (isOpen_lt hνc continuous_const).inter (isOpen_lt himc continuous_const)
  have hUb : IsOpen Ub := (isOpen_lt continuous_const hνc).union (isOpen_lt continuous_const himc)
  have hdisj : Disjoint Ua Ub := by
    rw [Set.disjoint_left]
    rintro t ⟨h1, h2⟩ (h3 | h3)
    · exact lt_asymm h1 h3
    · exact lt_asymm h2 h3
  have hcov : ehLeftEnergyComponent μ c ⊆ Ua ∪ Ub := by
    intro t ht
    have hG : ehLeftHamiltonian μ c t = 0 := G_zero_of_mem ht
    by_contra hno
    simp only [Set.mem_union, Set.mem_setOf_eq, Ua, Ub, not_or, not_and_or, not_lt] at hno
    obtain ⟨hA, hB1, hB2⟩ := hno
    have hcs := EHTrig.cosh_sub_cos (zC t)
    rcases hB2.lt_or_eq with him | him
    · -- `|Im ξ| < π`, hence `ν = r`, and `t` maps to a point on the forbidden circle
      have hνr : ν t = r := by
        rcases hA with h | h
        · exact le_antisymm hB1 h
        · exact absurd him (not_lt.2 h)
      have ht' : t ∈ targetEH := ⟨him, by simp only [hν] at hνr; rw [hνr]; exact hr1⟩
      have hloc := fromEH_mem_locus ht' hG
      apply hcirc _ hloc
      rw [position_radius_eq, two_zNormSq_fromEH]
      simp only [hν] at hνr; rw [hνr]
    · -- `|Im ξ| = π`: then `ν ≥ 1 > r`
      have hcos : Real.cos (zC t).im = -1 := by
        rcases abs_eq (Real.pi_pos.le) |>.1 him with h | h
        · rw [h, Real.cos_pi]
        · rw [h, Real.cos_neg, Real.cos_pi]
      have hge : 1 ≤ ν t := by
        simp only [hν]
        have := Real.one_le_cosh (zC t).re
        have hh : (zC t / 2) = zC t / 2 := rfl
        linarith [hcs, hcos]
      linarith
  have h0 : ehLeftCollisionPoint μ ∈ ehLeftEnergyComponent μ c :=
    mem_connectedComponentIn (by
      rw [← toEH_leftCollisionPoint hμ1]
      show ehLeftHamiltonian μ c (toEH μ (leftCollisionPoint μ)) = 0
      have hl := leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1
      rw [G_toEH μ c (component_subset_source hμ0 hμ1 hc hl),
        (mem_locus_of_component hl).1, mul_zero])
  have hz0 : zC (ehLeftCollisionPoint μ) = 0 := by
    apply Complex.ext <;> simp [zC, ehLeftCollisionPoint]
  have hsub : ehLeftEnergyComponent μ c ⊆ Ua :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hUa hUb hdisj hcov
      ⟨_, h0, by simp [Ua, hν, hz0, hr0, Real.pi_pos]⟩
  intro t ht
  obtain ⟨h1, h2⟩ := hsub ht
  exact ⟨h2, lt_trans h1 hr1⟩

theorem eh_subset_image {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ehLeftEnergyComponent μ c ⊆ toEH μ '' leftEnergyComponent μ c := by
  have htarget := eh_subset_target hμ0 hμ1 hc
  have hl := leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1
  have hlsrc := component_subset_source hμ0 hμ1 hc hl
  have himg : fromEH μ '' ehLeftEnergyComponent μ c ⊆ leftEnergyComponent μ c := by
    apply IsPreconnected.subset_connectedComponentIn
    · exact isPreconnected_connectedComponentIn.image _
        ((contDiffOn_fromEH μ (n := 0)).continuousOn.mono htarget)
    · refine ⟨ehLeftCollisionPoint μ, ?_, ?_⟩
      · exact (image_subset_eh hμ0 hμ1 hc) ⟨_, hl, toEH_leftCollisionPoint hμ1⟩
      · rw [← toEH_leftCollisionPoint hμ1, fromEH_toEH μ hlsrc]
    · rintro _ ⟨t, ht, rfl⟩
      exact fromEH_mem_locus (htarget ht) (G_zero_of_mem ht)
  intro t ht
  exact ⟨fromEH μ t, himg ⟨t, ht, rfl⟩, toEH_fromEH μ (htarget ht)⟩

theorem image_eq_eh {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    toEH μ '' leftEnergyComponent μ c = ehLeftEnergyComponent μ c :=
  (image_subset_eh hμ0 hμ1 hc).antisymm (eh_subset_image hμ0 hμ1 hc)

/-- The elliptic-hyperbolic regularization model of the selected Levi-Civita component. -/
def ehModel (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c) :
    RegularizationModel μ c where
  source := sourceEH
  target := targetEH
  source_open := isOpen_sourceEH
  target_open := isOpen_targetEH
  contains_component := component_subset_source hμ0 hμ1 hc
  toModel := toEH μ
  fromModel := fromEH μ
  toModel_mapsTo := fun _ hs => toEH_mem_target μ hs
  fromModel_mapsTo := fun _ ht => fromEH_mem_source μ ht
  left_inverse := fun _ hs => fromEH_toEH μ hs
  right_inverse := fun _ ht => toEH_fromEH μ ht
  toModel_smooth := contDiffOn_toEH μ
  fromModel_smooth := contDiffOn_fromEH μ
  symplecticScale := 4
  symplecticScale_pos := by norm_num
  symplectic := fun _ hs v w => toEH_symplectic μ hs v w
  antipodal := fun _ hs => toEH_neg μ (component_subset_source hμ0 hμ1 hc hs)
  modelHamiltonian := ehLeftHamiltonian μ c
  model_smooth := (contDiff_G μ c).contDiffOn
  model_zero := fun s hs => by
    rw [G_toEH μ c (component_subset_source hμ0 hμ1 hc hs),
      (mem_locus_of_component hs).1, mul_zero]
  model_regular := fun s hs h0 => by
    have hsrc := component_subset_source hμ0 hμ1 hc hs
    apply left_energy_component_regular μ c hμ0 hμ1 hc s hs
    ext v
    have := dG_comp_dPhi μ c hsrc (mem_locus_of_component hs).1 v
    rw [h0, ContinuousLinearMap.zero_apply] at this
    have hk := kappa_pos hsrc
    simp only [ContinuousLinearMap.zero_apply]
    rcases mul_eq_zero.1 this.symm with h | h
    · linarith
    · exact h
  timeScale := fun s => 4 / kappa s
  timeScale_continuous := by
    apply ContinuousOn.div continuousOn_const
    · unfold kappa; exact (continuous_const.mul
        (Real.continuous_sqrt.comp (by unfold secondCollisionDistanceSq; fun_prop))).continuousOn
    · intro s hs; exact (kappa_pos hs).ne'
  timeScale_pos := fun s hs => div_pos (by norm_num) (kappa_pos (component_subset_source hμ0 hμ1 hc hs))
  vectorField := fun s hs => vectorField_toEH μ c (component_subset_source hμ0 hμ1 hc hs)
    (mem_locus_of_component hs).1

end

end EHReg

end BirkhoffGlobalSection

/-!
# Localization of the near-critical EH component (child B)

1. *Pinch.* The subcritical forbidden circle `|q + μ| = r` (accepted
   `inner_lagrange_subcritical_circle_forbidden`) has `r < 1/2 + δ` near `(1/2, 2)`: otherwise the
   axis point at distance `r` from the left primary lies in the Hill region, and an explicit
   momentum puts it on the zero level.
2. *Radius.* The Levi-Civita component lies inside the forbidden circle; in EH coordinates
   `|q + μ| = (cosh x₁ - cos x₂)/2`, so `cosh x₁ - cos x₂ < 1 + 2δ` on the EH component.
3. *Hill region.* `G = 0` gives `V ≤ 0`; with `cos x₂ ≥ 0` this bounds `cosh x₁ ≤ 2` and the
   momenta, while `cos x₂ < 0` forces the point into any prescribed neighbourhood of the saddle.
-/

namespace BirkhoffGlobalSection.NearCriticalB

open BirkhoffGlobalSection BirkhoffGlobalSection.EHReg Complex

/-! ## 1. Pinching the forbidden radius -/

theorem axis_point_in_locus {μ c r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hΩ : c ≤ (r - μ) ^ 2 / 2 + (1 - μ) / r + μ / (1 - r)) :
    ∃ s ∈ regularEnergyLocus μ c,
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 + ((leviCivitaPosition μ s) 1) ^ 2 = r ^ 2 := by
  set ζ := Real.sqrt (r / 2) with hζ
  have hζ2 : ζ ^ 2 = r / 2 := Real.sq_sqrt (by linarith)
  have h1r : 0 < 1 - r := by linarith
  set B := ζ * (r - μ) with hB
  set C0 := c * ζ ^ 2 - (1 - μ) / 2 - μ * ζ ^ 2 / (1 - r) with hC0
  have hdisc : 0 ≤ B ^ 2 - 2 * C0 := by
    have e : B ^ 2 - 2 * C0 = r * ((r - μ) ^ 2 / 2 + (1 - μ) / r + μ / (1 - r) - c) := by
      rw [hB, hC0, mul_pow, hζ2]; field_simp; ring
    rw [e]; exact mul_nonneg hr0.le (by linarith)
  set w := -B + Real.sqrt (B ^ 2 - 2 * C0) with hw
  have hwq : w ^ 2 / 2 + B * w + C0 = 0 := by
    have hs := Real.sq_sqrt hdisc
    have : (w + B) ^ 2 = B ^ 2 - 2 * C0 := by
      rw [hw, show -B + Real.sqrt (B ^ 2 - 2 * C0) + B = Real.sqrt (B ^ 2 - 2 * C0) by ring, hs]
    nlinarith
  refine ⟨![ζ, 0, 0, w], ⟨?_, ?_⟩, ?_⟩
  · have hD : Real.sqrt (secondCollisionDistanceSq ![ζ, 0, 0, w]) = 1 - r := by
      have : secondCollisionDistanceSq ![ζ, 0, 0, w] = (1 - r) ^ 2 := by
        simp [secondCollisionDistanceSq]; rw [hζ2]; ring
      rw [this, Real.sqrt_sq h1r.le]
    have hK : leviCivitaHamiltonian μ c ![ζ, 0, 0, w] = w ^ 2 / 2 + B * w + C0 := by
      unfold leviCivitaHamiltonian
      rw [hD]
      simp only [zNormSq, wNormSq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [hB, hC0]
      linear_combination (2 * ζ * w) * hζ2
    rw [hK, hwq]
  · simp [secondCollisionDistanceSq]; rw [hζ2]; nlinarith
  · simp [leviCivitaPosition]; rw [hζ2]; ring

theorem pinch {μ c r δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hμ : |μ - 1 / 2| ≤ δ ^ 2 / 8) (hc : c < 2 + 4 * δ ^ 2) (hr0 : 0 < r) (hr1 : r < 1)
    (hforb : ∀ s ∈ regularEnergyLocus μ c,
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 + ((leviCivitaPosition μ s) 1) ^ 2 ≠ r ^ 2) :
    r < 1 / 2 + δ := by
  by_contra h
  push Not at h
  have h1r : 0 < 1 - r := by linarith
  have hd := abs_le.mp hμ
  have hrr : r * (1 - r) ≤ 1 / 4 - δ ^ 2 := by nlinarith
  have key : (2 + 4 * δ ^ 2) * (r * (1 - r)) ≤ (1 - μ) * (1 - r) + μ * r := by
    have e : (1 - μ) * (1 - r) + μ * r = 1 / 2 + (μ - 1 / 2) * (2 * r - 1) := by ring
    rw [e]
    have h2r : 0 ≤ 2 * r - 1 := by linarith
    have h2r1 : 2 * r - 1 ≤ 1 := by linarith
    nlinarith [mul_nonneg h2r (by linarith : (0 : ℝ) ≤ δ ^ 2 / 8 + (μ - 1 / 2)),
      mul_nonneg (sub_nonneg.mpr h2r1) (by linarith : (0 : ℝ) ≤ δ ^ 2 / 8 - (μ - 1 / 2)),
      mul_le_mul_of_nonneg_left hrr (by positivity : (0 : ℝ) ≤ 2 + 4 * δ ^ 2),
      sq_nonneg δ, pow_le_pow_left₀ hδ0.le hδ1 2]
  have hΩ : c ≤ (r - μ) ^ 2 / 2 + (1 - μ) / r + μ / (1 - r) := by
    have e : (1 - μ) / r + μ / (1 - r) = ((1 - μ) * (1 - r) + μ * r) / (r * (1 - r)) := by
      field_simp
    have hpos : 0 < r * (1 - r) := mul_pos hr0 h1r
    have : 2 + 4 * δ ^ 2 ≤ (1 - μ) / r + μ / (1 - r) := by
      rw [e, le_div_iff₀ hpos]; exact key
    nlinarith [sq_nonneg (r - μ)]
  obtain ⟨s, hs, hq⟩ := axis_point_in_locus hr0 hr1 hΩ
  exact hforb s hs hq

/-! ## 2. The component lies inside the forbidden circle -/

theorem component_inside {μ c r : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (hr0 : 0 < r)
    (hforb : ∀ s ∈ regularEnergyLocus μ c,
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 + ((leviCivitaPosition μ s) 1) ^ 2 ≠ r ^ 2) :
    ∀ s ∈ leftEnergyComponent μ c, 2 * zNormSq s < r := by
  intro s hs
  have hbase := leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1
  have hpre : IsPreconnected (leftEnergyComponent μ c) := isPreconnected_connectedComponentIn
  have hcont : Continuous fun s : Phase => (2 * zNormSq s) ^ 2 := by unfold zNormSq; fun_prop
  have h0 : (2 * zNormSq (leftCollisionPoint μ)) ^ 2 = 0 := by
    simp [zNormSq, leftCollisionPoint]
  have hz0 : 0 ≤ 2 * zNormSq s := by unfold zNormSq; positivity
  by_contra hlt
  push Not at hlt
  have hiv := hpre.intermediate_value hbase hs hcont.continuousOn
  rw [h0] at hiv
  obtain ⟨s', hs', he⟩ := hiv (show r ^ 2 ∈ Set.Icc 0 ((2 * zNormSq s) ^ 2) from
    ⟨by positivity, by nlinarith⟩)
  apply hforb s' (mem_locus_of_component hs')
  rw [position_radius_eq]; exact he

/-! ## 3. EH coordinates of the distance to the left primary -/

theorem normSq_sinh_re_im (a b : ℝ) :
    normSq (Complex.sinh ((a : ℂ) + (b : ℂ) * I)) = Real.sinh a ^ 2 + Real.sin b ^ 2 := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin]
  have e : (Real.sinh a : ℂ) * (Real.cos b : ℂ) + (Real.cosh a : ℂ) * ((Real.sin b : ℂ) * I) =
      ((Real.sinh a * Real.cos b : ℝ) : ℂ) + ((Real.cosh a * Real.sin b : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e, normSq_add_mul_I, mul_pow, mul_pow, Real.cosh_sq]
  nlinarith [Real.sin_sq_add_cos_sq b]

theorem normSq_sinh_half (t : Phase) :
    normSq (Complex.sinh (zC t / 2)) = (Real.cosh (t 0) - Real.cos (t 1)) / 2 := by
  have hz : zC t / 2 = ((t 0 / 2 : ℝ) : ℂ) + ((t 1 / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [zC]
  rw [hz, normSq_sinh_re_im]
  have h1 : Real.cosh (t 0) = 1 + 2 * Real.sinh (t 0 / 2) ^ 2 := by
    have := Real.cosh_two_mul (t 0 / 2)
    rw [show 2 * (t 0 / 2) = t 0 by ring] at this
    rw [this, Real.cosh_sq]; ring
  have h2 : Real.cos (t 1) = 1 - 2 * Real.sin (t 1 / 2) ^ 2 := by
    have := Real.cos_two_mul (t 1 / 2)
    rw [show 2 * (t 1 / 2) = t 1 by ring] at this
    rw [this, Real.cos_sq']; ring
  rw [h1, h2]; ring

/-- On the EH component, `cosh x₁ - cos x₂` is below twice the forbidden radius, and `|x₂| < π`. -/
theorem eh_component_radius {μ c r : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (hr0 : 0 < r)
    (hforb : ∀ s ∈ regularEnergyLocus μ c,
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 + ((leviCivitaPosition μ s) 1) ^ 2 ≠ r ^ 2)
    {y : Phase} (hy : y ∈ ehLeftEnergyComponent μ c) :
    Real.cosh (y 0) - Real.cos (y 1) < 2 * r ∧ |y 1| < Real.pi := by
  rw [← image_eq_eh hμ0 hμ1 hc] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  have hsrc := component_subset_source hμ0 hμ1 hc hs
  have hin := component_inside hμ0 hμ1 hc hr0 hforb s hs
  have ht := toEH_mem_target μ hsrc
  refine ⟨?_, ?_⟩
  · have e := two_zNormSq_fromEH μ (toEH μ s)
    rw [fromEH_toEH μ hsrc, normSq_sinh_half] at e
    linarith
  · have := ht.1; simpa [zC] using this

/-! ## 4. The first critical value near equal masses -/

theorem inv_sum_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) : 4 ≤ 1 / x + 1 / y := by
  rw [div_add_div _ _ hx.ne' hy.ne', le_div_iff₀ (mul_pos hx hy)]
  nlinarith [sq_nonneg (x - y)]

theorem first_critical_le (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    firstCriticalValue μ ≤ -2 + 4 * |μ - 1 / 2| := by
  obtain ⟨L, hL, hval⟩ := inner_lagrange_realizes_first_critical_value μ hμ0 hμ1
  obtain ⟨_, hcrit, hlo, hhi, h1⟩ := hL
  obtain ⟨h2, h3⟩ := jacobi_critical_momentum μ L hcrit
  rw [← hval]
  set x := L 0 + μ with hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < 1 - x := by linarith
  have hr1 : Real.sqrt ((L 0 + μ) ^ 2 + L 1 ^ 2) = x := by
    rw [h1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, ← hx, Real.sqrt_sq hx0.le]
  have hr2 : Real.sqrt ((L 0 - 1 + μ) ^ 2 + L 1 ^ 2) = 1 - x := by
    rw [h1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
      show (L 0 - 1 + μ) ^ 2 = (1 - x) ^ 2 by rw [hx]; ring, Real.sqrt_sq hy0.le]
  have hH : jacobiHamiltonian μ L = -(L 0) ^ 2 / 2 - (1 - μ) / x - μ / (1 - x) := by
    unfold jacobiHamiltonian
    rw [hr1, hr2, h2, h3, h1]
    ring
  rw [hH]
  have hinv := inv_sum_ge hx0 hy0 (by ring)
  have hd : |μ - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
  have hk : 0 ≤ 1 / 2 - |μ - 1 / 2| := by linarith
  have e1 : (1 / 2 - |μ - 1 / 2|) * (1 / x) ≤ (1 - μ) / x := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith [le_abs_self (μ - 1 / 2)]
  have e2 : (1 / 2 - |μ - 1 / 2|) * (1 / (1 - x)) ≤ μ / (1 - x) := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ hy0.le
    linarith [neg_abs_le (μ - 1 / 2)]
  have e3 : (1 / 2 - |μ - 1 / 2|) * 4 ≤ (1 / 2 - |μ - 1 / 2|) * (1 / x + 1 / (1 - x)) :=
    mul_le_mul_of_nonneg_left hinv hk
  nlinarith [sq_nonneg (L 0)]

/-! ## 5. The EH potential -/

/-- The EH potential in the variables `a = cosh x₁`, `b = cos x₂`. -/
noncomputable def Vm (μ c a b : ℝ) : ℝ :=
  c * (a ^ 2 - b ^ 2) / 4 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 - b ^ 2 * (1 - b ^ 2) / 32 +
    (1 - 2 * μ) * (-b / 2 - (1 / 2 - μ - a * b) * (a ^ 2 - b ^ 2) / 16)

theorem G_split (μ c : ℝ) (y : Phase) :
    ehLeftHamiltonian μ c y =
      ((y 2 + Real.sin (2 * y 1) / 8) ^ 2 + (y 3 + Real.sinh (2 * y 0) / 8) ^ 2) / 2 +
        Vm μ c (Real.cosh (y 0)) (Real.cos (y 1)) := by
  unfold ehLeftHamiltonian Vm
  simp only
  rw [EHConvex.sinh_two_sq, EHConvex.sin_two_sq]
  ring

/-- The `μ`-perturbation is small. -/
theorem pert_le {μ a b δ : ℝ} (hδ0 : 0 < δ) (hd : |μ - 1 / 2| ≤ δ ^ 2 / 8) (hδ : δ ≤ 1 / 64)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 21 / 10) (hb : |b| ≤ 1) :
    |(1 - 2 * μ) * (-b / 2 - (1 / 2 - μ - a * b) * (a ^ 2 - b ^ 2) / 16)| ≤ δ ^ 2 / 2 := by
  have hb' := abs_le.mp hb
  have hd' := abs_le.mp hd
  have hδ2 : δ ^ 2 ≤ 1 / 4096 := by
    have := pow_le_pow_left₀ hδ0.le hδ 2; norm_num at this; linarith
  have hm : |1 - 2 * μ| ≤ δ ^ 2 / 4 := by
    rw [abs_le]; constructor <;> linarith
  have hin : |-b / 2 - (1 / 2 - μ - a * b) * (a ^ 2 - b ^ 2) / 16| ≤ 2 := by
    rw [abs_le]; constructor <;>
      nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (by linarith : (0 : ℝ) ≤ 21 / 10 - a),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + b) (by linarith : (0 : ℝ) ≤ 1 - b),
        sq_nonneg b, sq_nonneg a, mul_nonneg (by linarith : (0 : ℝ) ≤ a) (sq_nonneg b),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ a))
          (by linarith : (0 : ℝ) ≤ 1 + b),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ a))
          (by linarith : (0 : ℝ) ≤ 1 - b)]
  rw [abs_mul]
  calc |1 - 2 * μ| * |-b / 2 - (1 / 2 - μ - a * b) * (a ^ 2 - b ^ 2) / 16|
      ≤ δ ^ 2 / 4 * 2 := mul_le_mul hm hin (abs_nonneg _) (by positivity)
    _ = δ ^ 2 / 2 := by ring

set_option maxHeartbeats 1600000 in
/-- Box case: `cos x₂ ≥ 0` forces `cosh x₁ ≤ 2` and bounds the potential. -/
theorem box_case {μ c a b δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 64) (hd : |μ - 1 / 2| ≤ δ ^ 2 / 8)
    (hc1 : 2 - δ ^ 2 / 2 ≤ c) (hc2 : c ≤ 2 + 4 * δ ^ 2)
    (ha1 : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : a - b < 1 + 2 * δ) (hV : Vm μ c a b ≤ 0) :
    a ≤ 2 ∧ -Vm μ c a b ≤ 2 := by
  have ha3 : a ≤ 21 / 10 := by linarith
  obtain ⟨hp1, hp2⟩ := abs_le.mp (pert_le (μ := μ) (a := a) (b := b) hδ0 hd hδ ha1 ha3 (by rw [abs_le]; constructor <;> linarith))
  have hδ2 : δ ^ 2 ≤ 1 / 4096 := by
    have := pow_le_pow_left₀ hδ0.le hδ 2; norm_num at this; linarith
  have ha2 : a ≤ 2 := by
    by_contra h
    push Not at h
    have hb2 : 1 - 2 * δ < b := by linarith
    have hb3 : 9 / 10 ≤ b := by linarith
    have hpos : 0 < Vm μ c a b := by
      unfold Vm
      have hcc : 199 / 100 ≤ c := by linarith
      have hab2 : 3 ≤ a ^ 2 - b ^ 2 := by nlinarith
      have hA : a ^ 2 * (a ^ 2 - 1) ≤ 133 / 10 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ 21 / 10 - a)]
      have hC : 199 / 100 * 3 ≤ c * (a ^ 2 - b ^ 2) := by nlinarith
      have hb4 : 81 / 100 ≤ b ^ 2 := by nlinarith
      have hb5 : b ^ 2 ≤ 1 := by nlinarith
      have hB2 : b ^ 2 * (1 - b ^ 2) ≤ 2 / 10 := by
        nlinarith [mul_le_mul hb5 (by linarith : 1 - b ^ 2 ≤ 19 / 100) (by linarith) (by norm_num)]
      nlinarith
    linarith
  refine ⟨ha2, ?_⟩
  unfold Vm at hV ⊢
  have hcpos : 0 ≤ c * (a ^ 2 - b ^ 2) := mul_nonneg (by linarith) (by nlinarith)
  have hA : a ^ 2 * (a ^ 2 - 1) ≤ 12 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ 2 - a)]
  have hB : b ^ 2 * (1 - b ^ 2) ≤ 1 / 4 := by nlinarith [sq_nonneg (b ^ 2 - 1 / 2)]
  have hB0 : 0 ≤ b ^ 2 * (1 - b ^ 2) := mul_nonneg (sq_nonneg b) (by nlinarith)
  nlinarith

/-- Neck case: `cos x₂ < 0` forces `(a, b)` near `(1, 0)` and the potential near `0`. -/
theorem neck_case {μ c a b δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 64) (hd : |μ - 1 / 2| ≤ δ ^ 2 / 8)
    (hc1 : 2 - δ ^ 2 / 2 ≤ c) (hc2 : c ≤ 2 + 4 * δ ^ 2)
    (ha1 : 1 ≤ a) (hb0 : b < 0) (hb1 : -1 ≤ b) (hab : a - b < 1 + 2 * δ) :
    a < 1 + 2 * δ ∧ -b < 2 * δ ∧ -Vm μ c a b ≤ δ := by
  have ha : a < 1 + 2 * δ := by linarith
  have hb : -b < 2 * δ := by linarith
  refine ⟨ha, hb, ?_⟩
  have ha3 : a ≤ 21 / 10 := by linarith
  obtain ⟨hp1, hp2⟩ := abs_le.mp (pert_le (μ := μ) (a := a) (b := b) hδ0 hd hδ ha1 ha3 (by rw [abs_le]; constructor <;> linarith))
  have hδ2 : δ ^ 2 ≤ δ / 64 := by nlinarith
  unfold Vm
  have hα : 0 ≤ a - 1 := by linarith
  have hb2 : b ^ 2 ≤ 4 * δ ^ 2 := by nlinarith
  have hcc : 0 ≤ c := by linarith
  have h1 : -(c * (a ^ 2 - b ^ 2) / 4) + a / 2 ≤ 3 * δ ^ 2 := by
    nlinarith [mul_nonneg hα (by linarith : (0 : ℝ) ≤ a), mul_nonneg hcc (sq_nonneg b),
      mul_le_mul_of_nonneg_right hc1 (by nlinarith : (0 : ℝ) ≤ a ^ 2)]
  have ha5 : a ^ 2 - 1 ≤ 5 * δ := by nlinarith
  have ha6 : a ^ 2 ≤ 2 := by nlinarith
  have h2 : a ^ 2 * (a ^ 2 - 1) / 32 ≤ δ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ha5 (sq_nonneg a)]
  have h3 : b ^ 2 * (1 - b ^ 2) / 32 ≤ δ ^ 2 := by
    nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) (sq_nonneg b)]
  nlinarith

theorem sq_sub_le (p s : ℝ) : (p - s) ^ 2 ≤ 2 * p ^ 2 + 2 * s ^ 2 := by
  nlinarith [sq_nonneg (p + s)]

theorem neck_a_bounds {a δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 64) (ha1 : 1 ≤ a)
    (ha : a < 1 + 2 * δ) : a ^ 2 - 1 ≤ 5 * δ ∧ a ^ 2 ≤ 2 ∧ 4 * a ^ 2 * (a ^ 2 - 1) ≤ 40 * δ := by
  have h1 : a ^ 2 - 1 ≤ 5 * δ := by nlinarith
  have h2 : a ^ 2 ≤ 2 := by nlinarith
  refine ⟨h1, h2, ?_⟩
  nlinarith [mul_le_mul h2 h1 (by nlinarith) (by norm_num)]

theorem neck_b_bound {b δ : ℝ} (hb0 : b < 0) (hbn : -b < 2 * δ) (hb1 : -1 ≤ b) :
    4 * b ^ 2 * (1 - b ^ 2) ≤ 16 * δ ^ 2 := by
  have : b ^ 2 ≤ 4 * δ ^ 2 := by nlinarith
  nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) (sq_nonneg b)]

/-! ## 6. Near the saddle -/

theorem one_add_sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have hs : |x / 2| ≤ |Real.sinh (x / 2)| := by
    rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hs2 : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rw [← sq_abs, ← sq_abs (Real.sinh _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  rw [h, Real.cosh_sq]
  nlinarith

theorem near_saddle_x2 {x : ℝ} {δ : ℝ} (hx : |x| < Real.pi) (hb : Real.cos x < 0)
    (hb2 : -Real.cos x < 2 * δ) :
    Real.pi / 2 < |x| ∧ |x| - Real.pi / 2 < Real.pi * δ := by
  have hcx : Real.cos x = Real.cos |x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.cos_neg]
  have hgt : Real.pi / 2 < |x| := by
    by_contra h; push Not at h
    have := Real.cos_nonneg_of_mem_Icc (show |x| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [abs_nonneg x, Real.pi_pos], h⟩)
    linarith
  refine ⟨hgt, ?_⟩
  set t := |x| - Real.pi / 2 with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ Real.pi / 2 := by linarith
  have hsin : Real.sin t = -Real.cos x := by
    rw [hcx, show |x| = t + Real.pi / 2 by linarith, Real.cos_add_pi_div_two]; ring
  have hj := Real.mul_le_sin ht0 ht1
  rw [hsin] at hj
  have hpi := Real.pi_pos
  have : 2 / Real.pi * t < 2 * δ := lt_of_le_of_lt hj hb2
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at this
  nlinarith

end BirkhoffGlobalSection.NearCriticalB

set_option maxHeartbeats 1600000 in
open BirkhoffGlobalSection BirkhoffGlobalSection.NearCriticalB BirkhoffGlobalSection.EHReg in
theorem solution (W : Set Phase) (hW : IsOpen W)
    (hplus : (![0, Real.pi / 2, 0, 0] : Phase) ∈ W)
    (hminus : (![0, -(Real.pi / 2), 0, 0] : Phase) ∈ W) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ y ∈ ehLeftEnergyComponent μ c, y ∉ W →
          Real.cosh (y 0) ^ 2 ≤ 4 ∧ |y 1| ≤ Real.pi / 2 ∧ |y 2| ≤ 12 ∧ |y 3| ≤ 12 := by
  obtain ⟨ρp, hρp, hbp⟩ := Metric.isOpen_iff.mp hW _ hplus
  obtain ⟨ρm, hρm, hbm⟩ := Metric.isOpen_iff.mp hW _ hminus
  set ρ := min (min ρp ρm) 1 with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hρp hρm) one_pos
  have hρp' : ρ ≤ ρp := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρm' : ρ ≤ ρm := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  set δ := min (1 / 64 : ℝ) (ρ ^ 2 / 8) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 64 := min_le_left _ _
  have hδρ : δ ≤ ρ ^ 2 / 8 := min_le_right _ _
  have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith
  refine ⟨δ ^ 2 / 8, 4 * δ ^ 2, by positivity, by positivity,
    fun μ c h0 h1 hμ hc hsub y hy hyW => ?_⟩
  have hd : |μ - 1 / 2| ≤ δ ^ 2 / 8 := hμ.le
  have hc1 : 2 - δ ^ 2 / 2 ≤ c := by
    have := first_critical_le μ h0 h1
    have hs : -c < firstCriticalValue μ := hsub
    linarith
  have hc2 : c ≤ 2 + 4 * δ ^ 2 := hc.le
  obtain ⟨r, hr0, hr1, hforb⟩ := inner_lagrange_subcritical_circle_forbidden μ c h0 h1 hsub
  have hrδ := pinch hδ0 (by linarith) hd hc hr0 hr1 hforb
  obtain ⟨hrad, hy1⟩ := eh_component_radius h0 h1 hsub hr0 hforb hy
  have hG := G_zero_of_mem hy
  rw [G_split] at hG
  set a := Real.cosh (y 0) with ha
  set b := Real.cos (y 1) with hb
  set P₁ := y 2 + Real.sin (2 * y 1) / 8 with hP₁
  set P₂ := y 3 + Real.sinh (2 * y 0) / 8 with hP₂
  have hab : a - b < 1 + 2 * δ := by linarith
  have hV : Vm μ c a b ≤ 0 := by linarith [sq_nonneg P₁, sq_nonneg P₂]
  have hP : P₁ ^ 2 + P₂ ^ 2 = -2 * Vm μ c a b := by linarith
  have ha1 : 1 ≤ a := Real.one_le_cosh _
  have hb1 : b ≤ 1 := Real.cos_le_one _
  have hbm1 : -1 ≤ b := Real.neg_one_le_cos _
  have hsh : Real.sinh (2 * y 0) ^ 2 = 4 * a ^ 2 * (a ^ 2 - 1) := EHConvex.sinh_two_sq _
  have hsn : Real.sin (2 * y 1) ^ 2 = 4 * b ^ 2 * (1 - b ^ 2) := EHConvex.sin_two_sq _
  by_cases hb0 : 0 ≤ b
  · obtain ⟨ha2, hVb⟩ := box_case hδ0 hδ1 hd hc1 hc2 ha1 hb0 hb1 hab hV
    have hP4 : P₁ ^ 2 + P₂ ^ 2 ≤ 4 := by linarith
    have hq1 : P₁ ^ 2 ≤ 2 ^ 2 := by have := sq_nonneg P₂; norm_num; linarith
    have hq2 : P₂ ^ 2 ≤ 2 ^ 2 := by have := sq_nonneg P₁; norm_num; linarith
    have hP1 : |P₁| ≤ 2 := abs_le.mpr (abs_le_of_sq_le_sq' hq1 (by norm_num))
    have hP2 : |P₂| ≤ 2 := abs_le.mpr (abs_le_of_sq_le_sq' hq2 (by norm_num))
    have ha4 : a ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ a) ha2 2; norm_num at this; exact this
    refine ⟨ha4, ?_, ?_, ?_⟩
    · by_contra h
      push Not at h
      have hcx : Real.cos (y 1) = Real.cos |y 1| := by
        rcases le_or_gt 0 (y 1) with h' | h'
        · rw [abs_of_nonneg h']
        · rw [abs_of_neg h', Real.cos_neg]
      have := Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [Real.pi_pos])
      rw [← hcx] at this
      linarith
    · have hs : |Real.sin (2 * y 1) / 8| ≤ 1 / 8 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
        exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by norm_num)
      have : y 2 = P₁ - Real.sin (2 * y 1) / 8 := by rw [hP₁]; ring
      rw [this]
      calc |P₁ - Real.sin (2 * y 1) / 8| ≤ |P₁| + |Real.sin (2 * y 1) / 8| := abs_sub _ _
        _ ≤ 12 := by linarith
    · have hs2 : Real.sinh (2 * y 0) ^ 2 ≤ 7 ^ 2 := by
        rw [hsh]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a) (by linarith : (0 : ℝ) ≤ 2 - a)]
      have hs : |Real.sinh (2 * y 0) / 8| ≤ 7 / 8 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact abs_le_of_sq_le_sq' hs2 (by norm_num) |> fun h => abs_le.mpr h
      have : y 3 = P₂ - Real.sinh (2 * y 0) / 8 := by rw [hP₂]; ring
      rw [this]
      calc |P₂ - Real.sinh (2 * y 0) / 8| ≤ |P₂| + |Real.sinh (2 * y 0) / 8| := abs_sub _ _
        _ ≤ 12 := by linarith
  · exfalso
    push Not at hb0
    obtain ⟨ha', hbn, hVn⟩ := neck_case hδ0 hδ1 hd hc1 hc2 ha1 hb0 hbm1 hab
    obtain ⟨hgt, ht⟩ := near_saddle_x2 hy1 hb0 hbn
    have hPs : P₁ ^ 2 + P₂ ^ 2 ≤ 2 * δ := by linarith
    have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
    -- coordinate bounds
    have hρsq : 0 < ρ ^ 2 := by positivity
    have hδsq : δ ^ 2 ≤ δ / 64 := by
      have := mul_le_mul_of_nonneg_left hδ1 hδ0.le; nlinarith
    have hx0 : y 0 ^ 2 < ρ ^ 2 := by
      have := one_add_sq_le_cosh (y 0)
      linarith
    have hx1 : |y 1| - Real.pi / 2 < ρ := by
      have : Real.pi * δ ≤ 4 * δ := mul_le_mul_of_nonneg_right hpi4 hδ0.le
      linarith
    have hx2 : y 2 ^ 2 < ρ ^ 2 := by
      have hsin : Real.sin (2 * y 1) ^ 2 ≤ 16 * δ ^ 2 := by
        rw [hsn]; exact neck_b_bound hb0 hbn hbm1
      have : y 2 = P₁ - Real.sin (2 * y 1) / 8 := by rw [hP₁]; ring
      rw [this]
      have key : (P₁ - Real.sin (2 * y 1) / 8) ^ 2 ≤
          2 * P₁ ^ 2 + 2 * (Real.sin (2 * y 1) ^ 2 / 64) := by
        have := sq_sub_le P₁ (Real.sin (2 * y 1) / 8); rw [div_pow] at this; norm_num at this ⊢
        linarith
      have := sq_nonneg P₂
      linarith
    have hx3 : y 3 ^ 2 < ρ ^ 2 := by
      have hsinh : Real.sinh (2 * y 0) ^ 2 ≤ 40 * δ := by
        rw [hsh]; exact (neck_a_bounds hδ0 hδ1 ha1 ha').2.2
      have : y 3 = P₂ - Real.sinh (2 * y 0) / 8 := by rw [hP₂]; ring
      rw [this]
      have key : (P₂ - Real.sinh (2 * y 0) / 8) ^ 2 ≤
          2 * P₂ ^ 2 + 2 * (Real.sinh (2 * y 0) ^ 2 / 64) := by
        have := sq_sub_le P₂ (Real.sinh (2 * y 0) / 8); rw [div_pow] at this; norm_num at this ⊢
        linarith
      have := sq_nonneg P₁
      linarith
    have habs : ∀ {t : ℝ}, t ^ 2 < ρ ^ 2 → |t| < ρ := fun h =>
      abs_lt.mpr (abs_lt_of_sq_lt_sq' h hρ0.le)
    rcases le_or_gt 0 (y 1) with hpos | hneg
    · apply hyW
      apply hbp
      rw [Metric.mem_ball, dist_pi_lt_iff hρp]
      intro i
      rw [Real.dist_eq]
      fin_cases i
      · simpa using lt_of_lt_of_le (habs hx0) hρp'
      · have e : |y 1| = y 1 := abs_of_nonneg hpos
        have : |y 1 - Real.pi / 2| < ρ := by
          rw [abs_lt]; constructor <;> linarith
        simpa using lt_of_lt_of_le this hρp'
      · simpa using lt_of_lt_of_le (habs hx2) hρp'
      · simpa using lt_of_lt_of_le (habs hx3) hρp'
    · apply hyW
      apply hbm
      rw [Metric.mem_ball, dist_pi_lt_iff hρm]
      intro i
      rw [Real.dist_eq]
      fin_cases i
      · simpa using lt_of_lt_of_le (habs hx0) hρm'
      · have e : |y 1| = -y 1 := abs_of_neg hneg
        have : |y 1 - -(Real.pi / 2)| < ρ := by
          rw [abs_lt]; constructor <;> linarith
        simpa using lt_of_lt_of_le this hρm'
      · simpa using lt_of_lt_of_le (habs hx2) hρm'
      · simpa using lt_of_lt_of_le (habs hx3) hρm'
