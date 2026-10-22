-- Prove2me | solution 1 for BirkhoffGlobalSection.regularization_model_convex_away_from_saddle_center
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T20:19:32.517773+00:00
-- url     : https://prove2.me/submissions/06713e51-0a1a-4709-bb3f-f46243d20a72

import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_forbidden
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_regular
import Definitions.Def_BirkhoffGlobalSection_EHRegularization_Map
import Theorems.Thm_BirkhoffGlobalSection_eh_critical_half_mass_strictly_convex_off_saddle
import Theorems.Thm_BirkhoffGlobalSection_eh_left_component_near_critical_in_box
import Theorems.Thm_BirkhoffGlobalSection_first_critical_value_near_half
import Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation

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
# Reduction of `regularization_model_convex_away_from_saddle_center`

The model is the elliptic-hyperbolic regularization `EHReg.ehModel` (coordinate map `toEH μ`).
Its saddle-centers `σ± = (0, ±π/2, 0, 0)` are carried by `fromEH (1/2)` to the Levi-Civita
points `(∓1/2, 0, 0, 0)`, so a neighbourhood `U` of the latter pulls back to a neighbourhood
`W` of `σ±` for all `μ` near `1/2`. Off `W` the selected EH component lies in the compact box
(child B); there, the strict convexity of the critical surface (child A) persists to nearby
parameters by the tube lemma; and subcritical energies near `μ = 1/2` are close to `2` (child C).
-/

namespace BirkhoffGlobalSection.NearCritical

open BirkhoffGlobalSection BirkhoffGlobalSection.EHConvex BirkhoffGlobalSection.EHReg
open Complex Filter Topology Set

noncomputable def sigP : Phase := ![0, Real.pi / 2, 0, 0]
noncomputable def sigM : Phase := ![0, -(Real.pi / 2), 0, 0]

theorem sinh_quarter_pi : Complex.sinh ((Real.pi / 4 : ℝ) * I) = (Real.sqrt 2 / 2 : ℝ) * I := by
  rw [Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_pi_div_four]

theorem zC_sigP : zC sigP / 2 = (Real.pi / 4 : ℝ) * I := by
  apply Complex.ext <;> simp [zC, sigP] <;> ring

theorem zC_sigM : zC sigM / 2 = (-(Real.pi / 4) : ℝ) * I := by
  apply Complex.ext <;> simp [zC, sigM] <;> ring

theorem sinh_sigP : Complex.sinh (zC sigP / 2) = (Real.sqrt 2 / 2 : ℝ) * I := by
  rw [zC_sigP, sinh_quarter_pi]

theorem sinh_sigM : Complex.sinh (zC sigM / 2) = (-(Real.sqrt 2 / 2) : ℝ) * I := by
  rw [zC_sigM, Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_neg, Real.sin_pi_div_four]

theorem sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]; positivity

theorem fromEH_sigP : fromEH (1 / 2) sigP = ![-(1 / 2), 0, 0, 0] := by
  have hw : wC sigP = 0 := by apply Complex.ext <;> simp [wC, sigP]
  have hz : I * Complex.sinh (zC sigP / 2) / (Real.sqrt 2 : ℂ) = -(1 / 2 : ℂ) := by
    rw [sinh_sigP]; field_simp
    rw [show (Real.sqrt 2 : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) from rfl]
    push_cast
    have : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt2_ne
    field_simp; ring_nf; simp [Complex.I_sq]
  simp only [fromEH, hw, hz]
  ext i; fin_cases i <;> simp [ofC]

theorem fromEH_sigM : fromEH (1 / 2) sigM = ![1 / 2, 0, 0, 0] := by
  have hw : wC sigM = 0 := by apply Complex.ext <;> simp [wC, sigM]
  have hz : I * Complex.sinh (zC sigM / 2) / (Real.sqrt 2 : ℂ) = (1 / 2 : ℂ) := by
    rw [sinh_sigM]; field_simp
    rw [show (Real.sqrt 2 : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) from rfl]
    push_cast
    have : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt2_ne
    field_simp; ring_nf; simp [Complex.I_sq]
  simp only [fromEH, hw, hz]
  ext i; fin_cases i <;> simp [ofC]

theorem sigP_mem_target : sigP ∈ targetEH := by
  refine ⟨?_, ?_⟩
  · simp [zC, sigP]; rw [abs_lt]; constructor <;> linarith [Real.pi_pos]
  · rw [sinh_sigP]; simp [Complex.normSq_apply]
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]

theorem sigM_mem_target : sigM ∈ targetEH := by
  refine ⟨?_, ?_⟩
  · simp [zC, sigM]; rw [abs_lt]; constructor <;> linarith [Real.pi_pos]
  · rw [sinh_sigM]; simp [Complex.normSq_apply]
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]

/-- `fromEH μ` differs from `fromEH (1/2)` by a term linear in `μ - 1/2`. -/
theorem ofC_add (a b a' b' : ℂ) : ofC a b + ofC a' b' = ofC (a + a') (b + b') := by
  ext i; fin_cases i <;> simp [ofC]

theorem fromEH_split (μ : ℝ) (t : Phase) :
    fromEH μ t = fromEH (1 / 2) t +
      ofC 0 (I * (((μ - 1 / 2 : ℝ) : ℂ) *
        (starRingEnd ℂ) (I * Complex.sinh (zC t / 2) / (Real.sqrt 2 : ℂ)))) := by
  rw [fromEH, fromEH, ofC_add]
  congr 1
  · ring
  · push_cast; ring

theorem continuous_ofC_zero : Continuous fun b : ℂ => ofC 0 b := by
  unfold ofC; fun_prop

theorem continuousAt_fromEH {σ : Phase} (hσ : σ ∈ targetEH) :
    ContinuousAt (fun p : ℝ × Phase => fromEH p.1 p.2) ((1 : ℝ) / 2, σ) := by
  have e : (fun p : ℝ × Phase => fromEH p.1 p.2) = fun p => fromEH (1 / 2) p.2 +
      ofC 0 (I * (((p.1 - 1 / 2 : ℝ) : ℂ) *
        (starRingEnd ℂ) (I * Complex.sinh (zC p.2 / 2) / (Real.sqrt 2 : ℂ)))) := by
    funext p; exact fromEH_split p.1 p.2
  rw [e]
  apply ContinuousAt.add
  · have hc : ContinuousAt (fromEH (1 / 2)) σ :=
      ((contDiffOn_fromEH (1 / 2) (n := 0)).continuousOn.continuousAt
        (isOpen_targetEH.mem_nhds hσ))
    exact ContinuousAt.comp (g := fromEH (1 / 2)) (f := fun p : ℝ × Phase => p.2)
      (x := ((1 : ℝ) / 2, σ)) hc continuous_snd.continuousAt
  · apply Continuous.continuousAt
    apply continuous_ofC_zero.comp
    have hz : Continuous fun p : ℝ × Phase => zC p.2 := continuous_zC.comp continuous_snd
    fun_prop

/-- Pull a Levi-Civita neighbourhood of `(∓1/2, 0, 0, 0)` back to an EH neighbourhood. -/
theorem exists_W (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U) (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ t, |μ - 1 / 2| < δ →
      (dist t sigP < δ ∨ dist t sigM < δ) → fromEH μ t ∈ U := by
  have hp : ∀ᶠ p in 𝓝 ((1 : ℝ) / 2, sigP), fromEH p.1 p.2 ∈ U :=
    (continuousAt_fromEH sigP_mem_target).eventually_mem
      (hU.mem_nhds (by show fromEH (1 / 2) sigP ∈ U; rw [fromEH_sigP]; exact hminus))
  have hm : ∀ᶠ p in 𝓝 ((1 : ℝ) / 2, sigM), fromEH p.1 p.2 ∈ U :=
    (continuousAt_fromEH sigM_mem_target).eventually_mem
      (hU.mem_nhds (by show fromEH (1 / 2) sigM ∈ U; rw [fromEH_sigM]; exact hplus))
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.eventually_nhds_iff.mp hp
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.eventually_nhds_iff.mp hm
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun μ t hμ ht => ?_⟩
  have hμ' : dist μ ((1 : ℝ) / 2) < min δ₁ δ₂ := by rw [Real.dist_eq]; exact hμ
  rcases ht with ht | ht
  · exact h₁ (y := (μ, t)) (by
      rw [Prod.dist_eq]
      exact max_lt (lt_of_lt_of_le hμ' (min_le_left _ _)) (lt_of_lt_of_le ht (min_le_left _ _)))
  · exact h₂ (y := (μ, t)) (by
      rw [Prod.dist_eq]
      exact max_lt (lt_of_lt_of_le hμ' (min_le_right _ _)) (lt_of_lt_of_le ht (min_le_right _ _)))

/-- Tube argument: tangential Hessian. -/
theorem eventually_hess {W : Set Phase} (hW : IsOpen W) (hp : sigP ∈ W) (hm : sigM ∈ W) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, 2),
      ∀ y ∈ (box 2 \ W) ×ˢ Metric.sphere (0 : Phase) 1,
        (ehLeftHamiltonian p.1 p.2 y.1 = 0 ∧
          fderiv ℝ (ehLeftHamiltonian p.1 p.2) y.1 y.2 = 0) →
        0 < fderiv ℝ (fun x => fderiv ℝ (ehLeftHamiltonian p.1 p.2) x y.2) y.1 y.2 := by
  have hcont : Continuous fun q : (ℝ × ℝ) × (Phase × Phase) =>
      ((q.1.1, q.1.2, q.2.1) : ℝ × ℝ × Phase) := by fun_prop
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase × Phase)
    (((isCompact_box 2).diff hW).prod (isCompact_sphere 0 1))
    (C := {q | Ghat (q.1.1, q.1.2, q.2.1) = 0 ∧
      fderiv ℝ Ghat (q.1.1, q.1.2, q.2.1) (L q.2.2) = 0})
    (IsClosed.inter (isClosed_eq (continuous_Ghat.comp hcont) continuous_const)
      (isClosed_eq ((continuous_fderiv_Ghat.comp hcont).clm_apply
        (L.continuous.comp (by fun_prop))) continuous_const))
    (Φ := fun q => fderiv ℝ (fderiv ℝ Ghat) (q.1.1, q.1.2, q.2.1) (L q.2.2) (L q.2.2))
    (((continuous_fderiv2_Ghat.comp hcont).clm_apply
        (L.continuous.comp (by fun_prop))).clm_apply (L.continuous.comp (by fun_prop)))
    (p₀ := ((1 : ℝ) / 2, 2))
    (fun y hy hC => by
      obtain ⟨⟨hb, hW'⟩, hsph⟩ := hy
      rw [← hess_G_eq]
      have hv : y.2 ≠ 0 := by
        intro h0; rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hsph; norm_num at hsph
      have hA := eh_critical_half_mass_strictly_convex_off_saddle y.1 hC.1 hb.2.1
        (by have := hb.1; norm_num at this ⊢; linarith)
        (fun e => hW' (e ▸ hp)) (fun e => hW' (e ▸ hm))
      exact hA.1.2 y.1 rfl y.2 hv (by rw [fderiv_G_apply]; exact hC.2))
  filter_upwards [h] with p hp' y hy hC
  rw [hess_G_eq]
  exact hp' y hy ⟨hC.1, by rw [← fderiv_G_apply]; exact hC.2⟩

/-- Tube argument: radial transversality. -/
theorem eventually_star {W : Set Phase} (hW : IsOpen W) (hp : sigP ∈ W) (hm : sigM ∈ W) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, 2),
      ∀ y ∈ box 2 \ W, ehLeftHamiltonian p.1 p.2 y = 0 →
        0 < fderiv ℝ (ehLeftHamiltonian p.1 p.2) y y := by
  have hcont : Continuous fun q : (ℝ × ℝ) × Phase => ((q.1.1, q.1.2, q.2) : ℝ × ℝ × Phase) := by
    fun_prop
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase)
    ((isCompact_box 2).diff hW)
    (C := {q | Ghat (q.1.1, q.1.2, q.2) = 0})
    (isClosed_eq (continuous_Ghat.comp hcont) continuous_const)
    (Φ := fun q => fderiv ℝ Ghat (q.1.1, q.1.2, q.2) (L q.2))
    ((continuous_fderiv_Ghat.comp hcont).clm_apply (L.continuous.comp continuous_snd))
    (p₀ := ((1 : ℝ) / 2, 2))
    (fun y hy hC => by
      obtain ⟨hb, hW'⟩ := hy
      rw [← fderiv_G_apply]
      exact (eh_critical_half_mass_strictly_convex_off_saddle y hC hb.2.1
        (by have := hb.1; norm_num at this ⊢; linarith)
        (fun e => hW' (e ▸ hp)) (fun e => hW' (e ▸ hm))).2)
  filter_upwards [h] with p hp' y hy hG
  rw [fderiv_G_apply]
  exact hp' y hy hG

theorem box_of {y : Phase}
    (h : Real.cosh (y 0) ^ 2 ≤ 4 ∧ |y 1| ≤ Real.pi / 2 ∧ |y 2| ≤ 12 ∧ |y 3| ≤ 12) :
    y ∈ box 2 := by
  refine ⟨by norm_num; exact h.1, h.2.1, by norm_num; exact h.2.2.1, by norm_num; exact h.2.2.2⟩

end BirkhoffGlobalSection.NearCritical

open BirkhoffGlobalSection BirkhoffGlobalSection.NearCritical BirkhoffGlobalSection.EHConvex
  BirkhoffGlobalSection.EHReg in
theorem solution
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∃ M : RegularizationModel μ c,
          ∀ s ∈ leftEnergyComponent μ c, s ∉ U →
            IsStrictlyConvexStarShapedAt M.modelHamiltonian (M.toModel s) := by
  obtain ⟨δ, hδ, hfrom⟩ := exists_W U hU hplus hminus
  set W : Set Phase := Metric.ball sigP δ ∪ Metric.ball sigM δ with hWdef
  have hW : IsOpen W := Metric.isOpen_ball.union Metric.isOpen_ball
  have hWp : sigP ∈ W := Or.inl (Metric.mem_ball_self hδ)
  have hWm : sigM ∈ W := Or.inr (Metric.mem_ball_self hδ)
  obtain ⟨ε₁, η₁, hε₁, hη₁, hB⟩ := eh_left_component_near_critical_in_box W hW hWp hWm
  obtain ⟨ε₂, η₂, hε₂, hη₂, hT⟩ := exists_eps_eta_of_eventually
    ((eventually_hess hW hWp hWm).and (eventually_star hW hWp hWm))
  obtain ⟨ε₃, hε₃, hC⟩ := first_critical_value_near_half η₂ hη₂
  refine ⟨min (min ε₁ ε₂) (min ε₃ δ), min η₁ η₂, by positivity, by positivity,
    fun μ c h0 h1 hμ hc hsub => ?_⟩
  have hμ₁ : |μ - 1 / 2| < ε₁ := lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hμ₂ : |μ - 1 / 2| < ε₂ := lt_of_lt_of_le hμ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hμ₃ : |μ - 1 / 2| < ε₃ := lt_of_lt_of_le hμ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hμδ : |μ - 1 / 2| < δ := lt_of_lt_of_le hμ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hc₁ : c < 2 + η₁ := lt_of_lt_of_le hc (by linarith [min_le_left η₁ η₂])
  have hc₂ : |c - 2| < η₂ := by
    have hlow := hC μ h0 h1 hμ₃
    have : -c < firstCriticalValue μ := hsub
    rw [abs_lt]; constructor
    · linarith
    · linarith [min_le_right η₁ η₂]
  obtain ⟨hhess, hstar⟩ := hT μ c hμ₂ hc₂
  refine ⟨ehModel μ c h0 h1 hsub, fun s hs hsU => ?_⟩
  show IsStrictlyConvexStarShapedAt (ehLeftHamiltonian μ c) (toEH μ s)
  set y := toEH μ s with hy
  have hsrc := component_subset_source h0 h1 hsub hs
  have hyc : y ∈ ehLeftEnergyComponent μ c := by
    rw [← image_eq_eh h0 h1 hsub]; exact ⟨s, hs, rfl⟩
  have hyW : y ∉ W := by
    intro hyW
    apply hsU
    have := hfrom μ y hμδ (by
      rcases hyW with h | h
      · exact Or.inl (Metric.mem_ball.mp h)
      · exact Or.inr (Metric.mem_ball.mp h))
    rwa [hy, fromEH_toEH μ hsrc] at this
  have hbox : y ∈ box 2 := box_of (hB μ c h0 h1 hμ₁ hc₁ hsub y hyc hyW)
  have hG : ehLeftHamiltonian μ c y = 0 := G_zero_of_mem hyc
  refine ⟨⟨fun z _ => (contDiff_G μ c).contDiffAt, fun z hz v hv htan => ?_⟩, hstar y ⟨hbox, hyW⟩ hG⟩
  rw [Set.mem_singleton_iff] at hz; subst hz
  set t : ℝ := ‖v‖⁻¹ with ht
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have htpos : 0 < t := inv_pos.mpr hnv
  have hw : t • v ∈ Metric.sphere (0 : Phase) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht,
      inv_mul_cancel₀ hnv.ne']
  have htan' : fderiv ℝ (ehLeftHamiltonian μ c) y (t • v) = 0 := by
    rw [map_smul, htan, smul_zero]
  have := hhess (y, t • v) ⟨⟨hbox, hyW⟩, hw⟩ ⟨hG, htan'⟩
  simp only at this
  rw [hess_G_eq] at this
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
  rw [hess_G_eq]
  have h2 : 0 < t * t := mul_pos htpos htpos
  nlinarith
