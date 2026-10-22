-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_regularization_model_low_energy_tail
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-02T21:46:46.549182+00:00
-- url     : https://prove2.me/submissions/d096cfe3-8fb9-446e-b4d9-1bfba5a77384

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Theorems.Thm_BirkhoffGlobalSection_positive_tangential_hessian_low_energy_tail
import Theorems.Thm_BirkhoffGlobalSection_star_shaped_level_set_convex
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_compact
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_regular
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_exists
import Theorems.Thm_BirkhoffGlobalSection_left_component_ray_unique_scale
import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_interior_negative
import Theorems.Thm_BirkhoffGlobalSection_left_component_radial_norm_positive
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_smoothAt_of_secondCollisionFree
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
# A convex regularization model on the very-negative-energy tail

On the tail the Levi-Civita coordinates themselves are a convex model. Given positive
tangential Hessian along the selected component `S` (the child
`positive_tangential_hessian_low_energy_tail`), we take the identity map, the
Levi-Civita Hamiltonian as model Hamiltonian and unit time scale.

* The body is the radial filling `{t s : s ∈ S, 0 ≤ t ≤ 1}`. It is compact, and convex
  by the Hadamard-type theorem `star_shaped_level_set_convex`. Its hypotheses are the
  accepted radial lemmas for the subcritical component, plus `K(0) = -(1-μ)/2 < 0`.
* The origin is interior: the Euclidean radius has a positive minimum `ρ₀` on the
  compact set `S`, and every point of norm below `ρ₀/2` is a fraction of the point of `S`
  on its ray.
* The frontier of the body is `S`. A point `t s` with `t < 1` lies on an open segment
  from the interior point `0` to the body, hence is interior. A point `s ∈ S` is not
  interior, since `(1+η) s` would then lie in the body, contradicting uniqueness of the
  ray intersection.
-/

open BirkhoffGlobalSection
open scoped ContDiff Topology

set_option autoImplicit false

/-- The radial filling of a set. -/
private def fill (S : Set Phase) : Set Phase :=
  {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}

/-- Euclidean radius in the four phase coordinates. -/
private noncomputable def erad (y : Phase) : ℝ := Real.sqrt (zNormSq y + wNormSq y)

private lemma continuous_erad : Continuous erad := by
  unfold erad zNormSq wNormSq; fun_prop

private lemma erad_smul (r : ℝ) (hr : 0 ≤ r) (y : Phase) : erad (r • y) = r * erad y := by
  unfold erad zNormSq wNormSq
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (r * y 0) ^ 2 + (r * y 1) ^ 2 + ((r * y 2) ^ 2 + (r * y 3) ^ 2) =
      r ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + (y 2 ^ 2 + y 3 ^ 2)) by ring,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

private lemma erad_le (y : Phase) : erad y ≤ 2 * ‖y‖ := by
  unfold erad zNormSq wNormSq
  have h : ∀ i, |y i| ≤ ‖y‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
  rw [Real.sqrt_le_left (by positivity)]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have hn := norm_nonneg y
  nlinarith [sq_abs (y 0), sq_abs (y 1), sq_abs (y 2), sq_abs (y 3),
    abs_nonneg (y 0), abs_nonneg (y 1), abs_nonneg (y 2), abs_nonneg (y 3),
    mul_self_le_mul_self (abs_nonneg (y 0)) h0, mul_self_le_mul_self (abs_nonneg (y 1)) h1,
    mul_self_le_mul_self (abs_nonneg (y 2)) h2, mul_self_le_mul_self (abs_nonneg (y 3)) h3]

private lemma erad_pos {y : Phase} (hy : y ≠ 0) : 0 < erad y := by
  unfold erad zNormSq wNormSq
  apply Real.sqrt_pos.2
  by_contra h
  push_neg at h
  apply hy
  funext i
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2),
    sq_nonneg (y 3)]

/-- Points written along a ray. -/
private lemma ray_eq (r : ℝ) (x : Phase) : (fun i : Fin 4 => r * x i) = r • x := rfl

private lemma normalize_sphere {y : Phase} (hy : y ≠ 0) : (erad y)⁻¹ • y ∈ unitThreeSphere := by
  have he := erad_pos hy
  show zNormSq ((erad y)⁻¹ • y) + wNormSq ((erad y)⁻¹ • y) = 1
  have hsq : erad y ^ 2 = zNormSq y + wNormSq y := by
    unfold erad
    exact Real.sq_sqrt (by unfold zNormSq wNormSq; positivity)
  unfold zNormSq wNormSq at hsq ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith

section Model

variable {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c)
include hμ0 hμ1 hc

private lemma comp_ne_zero {s : Phase} (hs : s ∈ leftEnergyComponent μ c) : s ≠ 0 := by
  intro h
  have := left_component_radial_norm_positive μ c hμ0 hμ1 hc s hs
  rw [h] at this
  simp [zNormSq, wNormSq] at this

private lemma fill_convex
    (hTH : HasPositiveTangentialHessianOn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c)) :
    Convex ℝ (fill (leftEnergyComponent μ c)) := by
  refine star_shaped_level_set_convex (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c)
    (left_energy_component_compact μ c hμ0 hμ1 hc)
    (fun s hs => (connectedComponentIn_subset _ _ hs).1)
    (left_energy_component_regular μ c hμ0 hμ1 hc) hTH
    (left_component_ray_exists μ c hμ0 hμ1 hc)
    (left_component_ray_unique_scale μ c hμ0 hμ1 hc) ?_
  intro x hx R hR hRx r hr0 hrR
  rcases hr0.lt_or_eq with hr | hr
  · exact left_component_radial_interior_negative μ c hμ0 hμ1 hc x hx R hR hRx r hr hrR
  · subst hr
    simp [leviCivitaHamiltonian, wNormSq, zNormSq]
    linarith

private lemma fill_compact : IsCompact (fill (leftEnergyComponent μ c)) := by
  have he : fill (leftEnergyComponent μ c) =
      (fun p : ℝ × Phase => p.1 • p.2) '' (Set.Icc (0 : ℝ) 1 ×ˢ leftEnergyComponent μ c) := by
    ext y
    constructor
    · rintro ⟨s, hs, t, ht0, ht1, rfl⟩
      exact ⟨(t, s), ⟨⟨ht0, ht1⟩, hs⟩, rfl⟩
    · rintro ⟨⟨t, s⟩, ⟨⟨ht0, ht1⟩, hs⟩, rfl⟩
      exact ⟨s, hs, t, ht0, ht1, rfl⟩
  rw [he]
  exact (isCompact_Icc.prod (left_energy_component_compact μ c hμ0 hμ1 hc)).image
    (continuous_fst.smul continuous_snd)

private lemma fill_origin : (0 : Phase) ∈ interior (fill (leftEnergyComponent μ c)) := by
  have hS := left_energy_component_compact μ c hμ0 hμ1 hc
  -- the component is nonempty
  obtain ⟨r1, hr1, hp1⟩ := left_component_ray_exists μ c hμ0 hμ1 hc ![1, 0, 0, 0]
    (by simp [unitThreeSphere, zNormSq, wNormSq])
  have hne : (leftEnergyComponent μ c).Nonempty := ⟨_, hp1⟩
  obtain ⟨s0, hs0, hmin⟩ := hS.exists_isMinOn hne continuous_erad.continuousOn
  set ρ0 := erad s0 with hρ0
  have hρ0pos : 0 < ρ0 := erad_pos (comp_ne_zero hμ0 hμ1 hc hs0)
  refine mem_interior.2 ⟨Metric.ball 0 (ρ0 / 2), fun y hy => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity)⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  by_cases hy0 : y = 0
  · exact ⟨s0, hs0, 0, le_rfl, zero_le_one, by simp [hy0]⟩
  · have hey := erad_pos hy0
    obtain ⟨r, hr, hp⟩ := left_component_ray_exists μ c hμ0 hμ1 hc _ (normalize_sphere hy0)
    rw [ray_eq] at hp
    have hrad : erad (r • (erad y)⁻¹ • y) = r := by
      rw [erad_smul r hr.le, erad_smul _ (inv_nonneg.2 hey.le), inv_mul_cancel₀ hey.ne', mul_one]
    have hrρ : ρ0 ≤ r := by
      have := hmin hp
      simpa [hrad] using this
    have hle := erad_le y
    refine ⟨r • (erad y)⁻¹ • y, hp, erad y / r, by positivity, ?_, ?_⟩
    · rw [div_le_one hr]; linarith
    · rw [smul_smul, smul_smul, show erad y / r * r * (erad y)⁻¹ = 1 by
        field_simp]
      simp

private lemma fill_frontier
    (hTH : HasPositiveTangentialHessianOn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c)) :
    frontier (fill (leftEnergyComponent μ c)) = leftEnergyComponent μ c := by
  have hconv := fill_convex hμ0 hμ1 hc hTH
  have horig := fill_origin hμ0 hμ1 hc
  have hclosed := (fill_compact hμ0 hμ1 hc).isClosed
  ext y
  constructor
  · intro hy
    have hy' : y ∈ fill (leftEnergyComponent μ c) := hclosed.closure_subset hy.1
    obtain ⟨s, hs, t, ht0, ht1, rfl⟩ := hy'
    rcases ht1.lt_or_eq with ht | ht
    · exfalso
      apply hy.2
      rcases ht0.lt_or_eq with ht0' | ht0'
      · apply hconv.openSegment_interior_closure_subset_interior horig
          (subset_closure ⟨s, hs, 1, zero_le_one, le_rfl, (one_smul ℝ s).symm⟩)
        exact ⟨1 - t, t, by linarith, ht0', by ring, by simp⟩
      · rw [← ht0', zero_smul]; exact horig
    · rw [ht, one_smul]; exact hs
  · intro hy
    refine ⟨subset_closure ⟨y, hy, 1, zero_le_one, le_rfl, (one_smul ℝ y).symm⟩, fun hint => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hint
    have hy0 := comp_ne_zero hμ0 hμ1 hc hy
    have hnorm : 0 < ‖y‖ := norm_pos_iff.2 hy0
    set η := ε / (2 * ‖y‖) with hη
    have hη0 : 0 < η := by positivity
    have hmem : (1 + η) • y ∈ fill (leftEnergyComponent μ c) := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, show (1 + η) • y - y = η • y by
        rw [add_smul, one_smul]; abel, norm_smul, Real.norm_of_nonneg hη0.le, hη]
      field_simp
      linarith
    obtain ⟨s', hs', t, ht0, ht1, hts⟩ := hmem
    have ht0' : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hts
      have : (1 + η) • y = 0 := hts
      rcases smul_eq_zero.1 this with h | h
      · linarith
      · exact hy0 h
    -- both points lie on the ray through `y`
    set x := (erad y)⁻¹ • y with hx
    have hsph := normalize_sphere hy0
    have hey := erad_pos hy0
    have hy_ray : (fun i : Fin 4 => erad y * x i) ∈ leftEnergyComponent μ c := by
      rw [ray_eq, hx, smul_smul, mul_inv_cancel₀ hey.ne', one_smul]; exact hy
    have hs'_ray : (fun i : Fin 4 => ((1 + η) / t * erad y) * x i) ∈
        leftEnergyComponent μ c := by
      rw [ray_eq, hx, smul_smul, show (1 + η) / t * erad y * (erad y)⁻¹ = (1 + η) / t by
        field_simp]
      have : s' = ((1 + η) / t) • y := by
        rw [div_eq_mul_inv, mul_comm, ← smul_smul, hts, smul_smul, inv_mul_cancel₀ ht0',
          one_smul]
      rw [← this]; exact hs'
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
    have heq := left_component_ray_unique_scale μ c hμ0 hμ1 hc x hsph (erad y)
      ((1 + η) / t * erad y) hey (by positivity) hy_ray hs'_ray
    have : (1 + η) / t = 1 := by
      field_simp at heq
      nlinarith
    rw [div_eq_one_iff_eq htpos.ne'] at this
    linarith

end Model

theorem solution :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        Nonempty (ConvexRegularizationModel μ c) := by
  obtain ⟨ε, C, hε, hA⟩ := positive_tangential_hessian_low_energy_tail
  refine ⟨ε, C, hε, fun μ c hμ0 hμ1 hμε hC hc => ?_⟩
  have hTH := hA μ c hμ0 hμ1 hμε hC hc
  have hFr := fill_frontier hμ0 hμ1 hc hTH
  exact ⟨{
    source := {s | 0 < secondCollisionDistanceSq s}
    target := {s | 0 < secondCollisionDistanceSq s}
    source_open := isOpen_lt continuous_const (by unfold secondCollisionDistanceSq; fun_prop)
    target_open := isOpen_lt continuous_const (by unfold secondCollisionDistanceSq; fun_prop)
    contains_component := fun s hs => (connectedComponentIn_subset _ _ hs).2
    toModel := id
    fromModel := id
    toModel_mapsTo := fun _ h => h
    fromModel_mapsTo := fun _ h => h
    left_inverse := fun _ _ => rfl
    right_inverse := fun _ _ => rfl
    toModel_smooth := contDiffOn_id
    fromModel_smooth := contDiffOn_id
    symplecticScale := 1
    symplecticScale_pos := one_pos
    symplectic := fun s _ v w => by simp
    antipodal := fun _ _ => rfl
    body := fill (leftEnergyComponent μ c)
    body_compact := fill_compact hμ0 hμ1 hc
    body_convex := fill_convex hμ0 hμ1 hc hTH
    origin_interior := fill_origin hμ0 hμ1 hc
    image_frontier := by rw [Set.image_id, hFr]
    modelHamiltonian := leviCivitaHamiltonian μ c
    model_smooth := fun s hs =>
      (leviCivita_smoothAt_of_secondCollisionFree μ c s hs).contDiffWithinAt
    model_zero := fun y hy => by
      rw [hFr] at hy; exact (connectedComponentIn_subset _ _ hy).1
    model_regular := fun y hy => by
      rw [hFr] at hy; exact left_energy_component_regular μ c hμ0 hμ1 hc y hy
    model_hessian := by rw [hFr]; exact hTH
    timeScale := fun _ => 1
    timeScale_continuous := continuousOn_const
    timeScale_pos := fun _ _ => one_pos
    vectorField := fun s _ => by simp }⟩
