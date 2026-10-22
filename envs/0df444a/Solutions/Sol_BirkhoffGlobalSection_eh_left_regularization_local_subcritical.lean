-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_regularization_local_subcritical
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T10:39:12.394025+00:00
-- url     : https://prove2.me/submissions/434e2ba5-5215-4d5a-89f6-1d52c724652d

import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_forbidden
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_regular
import Definitions.Def_BirkhoffGlobalSection_EHRegularization_Map

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

open BirkhoffGlobalSection in
theorem solution
    (c₀ : ℝ) (_hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∃ M : RegularizationModel μ c,
          M.modelHamiltonian = ehLeftHamiltonian μ c ∧
          M.toModel '' leftEnergyComponent μ c = ehLeftEnergyComponent μ c :=
  ⟨1, 1, one_pos, one_pos, fun μ c hμ0 hμ1 _ _ hc =>
    ⟨EHReg.ehModel μ c hμ0 hμ1 hc, rfl, EHReg.image_eq_eh hμ0 hμ1 hc⟩⟩
