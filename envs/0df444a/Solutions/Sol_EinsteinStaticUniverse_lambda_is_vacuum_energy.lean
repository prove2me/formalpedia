-- Prove2me | solution 1 for EinsteinStaticUniverse.lambda_is_vacuum_energy
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:22:57.962195+00:00
-- url     : https://prove2.me/submissions/d37f52af-f4f7-4868-8925-f2aee1fdc153

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

open EinsteinStaticUniverse

theorem W2c_EinsteinStaticUniverse_vacuum :
    (1.1e-52 : ℝ) * (1.616255e-35 : ℝ) ^ 2 < 1e-120 ∧
      (1e54 : ℝ) < (1e8 : ℝ) / (2.5e-47 : ℝ) := by
  constructor <;> norm_num

theorem W2c_EinsteinStaticUniverse_accel_formula (G Λ ρ₀ a₀ x : ℝ) (hx : x ≠ 0) :
    accel G Λ ρ₀ a₀ x = x / 3 * (Λ - 4 * Real.pi * G * ρ₀ * a₀ ^ 3 / x ^ 3) := by
  unfold accel dustDensity
  field_simp
  ring

theorem W2c_EinsteinStaticUniverse_Lam (G Λ ρ₀ a₀ aE : ℝ) (haE : 0 < aE)
    (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) :
    Λ = 4 * Real.pi * G * ρ₀ * a₀ ^ 3 / aE ^ 3 := by
  rw [hstatic]; unfold dustDensity; rw [div_pow]; ring

theorem W2c_EinsteinStaticUniverse_accel_pos (G Λ ρ₀ a₀ aE x : ℝ) (hG : 0 < G)
    (hρ₀ : 0 < ρ₀) (ha₀ : 0 < a₀) (haE : 0 < aE)
    (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) (hx : aE < x) :
    0 < accel G Λ ρ₀ a₀ x := by
  have hx0 : 0 < x := haE.trans hx
  rw [W2c_EinsteinStaticUniverse_accel_formula _ _ _ _ _ hx0.ne']
  have hK : 0 < 4 * Real.pi * G * ρ₀ * a₀ ^ 3 := by positivity
  have hΛ := W2c_EinsteinStaticUniverse_Lam G Λ ρ₀ a₀ aE haE hstatic
  have h3 : aE ^ 3 < x ^ 3 := by gcongr
  have h4 : 4 * Real.pi * G * ρ₀ * a₀ ^ 3 / x ^ 3 < Λ := by
    rw [hΛ]; exact div_lt_div_of_pos_left hK (by positivity) h3
  have h5 : 0 < x / 3 := by positivity
  exact mul_pos h5 (by linarith)

theorem W2c_EinsteinStaticUniverse_accel_neg (G Λ ρ₀ a₀ aE x : ℝ) (hG : 0 < G)
    (hρ₀ : 0 < ρ₀) (ha₀ : 0 < a₀) (haE : 0 < aE)
    (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) (hx0 : 0 < x) (hx : x < aE) :
    accel G Λ ρ₀ a₀ x < 0 := by
  rw [W2c_EinsteinStaticUniverse_accel_formula _ _ _ _ _ hx0.ne']
  have hK : 0 < 4 * Real.pi * G * ρ₀ * a₀ ^ 3 := by positivity
  have hΛ := W2c_EinsteinStaticUniverse_Lam G Λ ρ₀ a₀ aE haE hstatic
  have h3 : x ^ 3 < aE ^ 3 := by gcongr
  have h4 : Λ < 4 * Real.pi * G * ρ₀ * a₀ ^ 3 / x ^ 3 := by
    rw [hΛ]; exact div_lt_div_of_pos_left hK (by positivity) h3
  have h5 : 0 < x / 3 := by positivity
  exact mul_neg_of_pos_of_neg h5 (by linarith)

theorem W2c_EinsteinStaticUniverse_escape (G Λ ρ₀ a₀ aE : ℝ) (hG : 0 < G) (hρ₀ : 0 < ρ₀)
    (ha₀ : 0 < a₀)
    (haE : 0 < aE) (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) (a : ℝ → ℝ)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ a t)
    (hdiff₂ : ∀ t : ℝ, DifferentiableAt ℝ (deriv a) t)
    (heq : FriedmannII G Λ ρ₀ a₀ a (Set.Ici 0))
    (h₀ : aE < a 0) (h₀' : 0 ≤ deriv a 0) :
    StrictMonoOn a (Set.Ici 0) ∧ Filter.Tendsto a Filter.atTop Filter.atTop := by
  have hca : Continuous a := continuous_iff_continuousAt.2 fun t => (hdiff t).continuousAt
  have hcd : Continuous (deriv a) :=
    continuous_iff_continuousAt.2 fun t => (hdiff₂ t).continuousAt
  have key : ∀ t, 0 ≤ t → aE < a t := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t, ht0, hta⟩ := hcon
    let S : Set ℝ := {s | 0 ≤ s ∧ a s ≤ aE}
    have hSne : S.Nonempty := ⟨t, ht0, hta⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
    have hSclosed : IsClosed S :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_le hca continuous_const)
    have ht1S : sInf S ∈ S := hSclosed.csInf_mem hSne hSbdd
    have ht1pos : 0 < sInf S := by
      rcases ht1S.1.lt_or_eq with h | h
      · exact h
      · exfalso; have h2 := ht1S.2; rw [← h] at h2; linarith
    have hbelow : ∀ s, 0 ≤ s → s < sInf S → aE < a s := by
      intro s hs hst
      by_contra hc; push_neg at hc
      have : sInf S ≤ s := csInf_le hSbdd ⟨hs, hc⟩
      linarith
    have hmono1 : MonotoneOn (deriv a) (Set.Icc 0 (sInf S)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (sInf S)) hcd.continuousOn
        (fun s _ => (hdiff₂ s).differentiableWithinAt)
      intro s hs
      rw [interior_Icc] at hs
      rw [heq s (Set.mem_Ici.2 hs.1.le)]
      exact (W2c_EinsteinStaticUniverse_accel_pos G Λ ρ₀ a₀ aE _ hG hρ₀ ha₀ haE hstatic
        (hbelow s hs.1.le hs.2)).le
    have hmono2 : MonotoneOn a (Set.Icc 0 (sInf S)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (sInf S)) hca.continuousOn
        (fun s _ => (hdiff s).differentiableWithinAt)
      intro s hs
      rw [interior_Icc] at hs
      have := hmono1 ⟨le_refl 0, ht1pos.le⟩ ⟨hs.1.le, hs.2.le⟩ hs.1.le
      linarith
    have := hmono2 ⟨le_refl 0, ht1pos.le⟩ ⟨ht1pos.le, le_refl _⟩ ht1pos.le
    linarith [ht1S.2]
  have hdd : ∀ s, 0 ≤ s → 0 < deriv (deriv a) s := fun s hs => by
    rw [heq s (Set.mem_Ici.2 hs)]
    exact W2c_EinsteinStaticUniverse_accel_pos G Λ ρ₀ a₀ aE _ hG hρ₀ ha₀ haE hstatic (key s hs)
  have hsm1 : StrictMonoOn (deriv a) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcd.continuousOn
    intro s hs; rw [interior_Ici] at hs; exact hdd s (le_of_lt hs)
  have hdpos : ∀ s, 0 < s → 0 < deriv a s := fun s hs =>
    lt_of_le_of_lt h₀' (hsm1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.le) hs)
  have hsm : StrictMonoOn a (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hca.continuousOn
    intro s hs; rw [interior_Ici] at hs; exact hdpos s hs
  refine ⟨hsm, ?_⟩
  have hd1 := hdpos 1 one_pos
  have hlin : ∀ t, 1 ≤ t → a 1 + deriv a 1 * (t - 1) ≤ a t := by
    intro t ht
    have hm : MonotoneOn (fun s => a s - deriv a 1 * s) (Set.Ici 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      · exact (hca.sub (continuous_const.mul continuous_id)).continuousOn
      · intro s _
        exact ((hdiff s).sub ((differentiableAt_id).const_mul _)).differentiableWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        have e : deriv (fun s => a s - deriv a 1 * s) s = deriv a s - deriv a 1 := by
          have h1 : HasDerivAt (fun s => a s - deriv a 1 * s) (deriv a s - deriv a 1 * 1) s :=
            (hdiff s).hasDerivAt.sub ((hasDerivAt_id' s).const_mul (deriv a 1))
          rw [h1.deriv]; ring
        rw [e]
        have hs' : (1:ℝ) < s := hs
        have := hsm1.monotoneOn (show (1:ℝ) ∈ Set.Ici 0 by norm_num)
          (show s ∈ Set.Ici (0:ℝ) from Set.mem_Ici.2 (by linarith)) hs'.le
        linarith
    have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    try simp only at this
    linarith
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨max 1 (1 + (b - a 1) / deriv a 1), fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 1 + (b - a 1) / deriv a 1 ≤ t := le_trans (le_max_right _ _) ht
  have h3 := hlin t ht1
  have h4 : (b - a 1) / deriv a 1 * deriv a 1 = b - a 1 := div_mul_cancel₀ _ hd1.ne'
  have h5 : (b - a 1) / deriv a 1 * deriv a 1 ≤ (t - 1) * deriv a 1 :=
    mul_le_mul_of_nonneg_right (by linarith) hd1.le
  nlinarith

theorem W2c_EinsteinStaticUniverse_collapse (G Λ ρ₀ a₀ aE T : ℝ) (hG : 0 < G) (hρ₀ : 0 < ρ₀)
    (ha₀ : 0 < a₀) (haE : 0 < aE) (hT : 0 < T)
    (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) (a : ℝ → ℝ)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ a t)
    (hdiff₂ : ∀ t : ℝ, DifferentiableAt ℝ (deriv a) t)
    (hpos : ∀ t ∈ Set.Icc 0 T, 0 < a t)
    (heq : FriedmannII G Λ ρ₀ a₀ a (Set.Icc 0 T))
    (h₀ : a 0 < aE) (h₀' : deriv a 0 ≤ 0) :
    StrictAntiOn a (Set.Icc 0 T) := by
  have hca : Continuous a := continuous_iff_continuousAt.2 fun t => (hdiff t).continuousAt
  have hcd : Continuous (deriv a) :=
    continuous_iff_continuousAt.2 fun t => (hdiff₂ t).continuousAt
  have key : ∀ t, 0 ≤ t → t ≤ T → a t < aE := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t, ht0, htT, hta⟩ := hcon
    let S : Set ℝ := {s | 0 ≤ s ∧ s ≤ T ∧ aE ≤ a s}
    have hSne : S.Nonempty := ⟨t, ht0, htT, hta⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
    have hSclosed : IsClosed S :=
      (isClosed_le continuous_const continuous_id).inter
        ((isClosed_le continuous_id continuous_const).inter (isClosed_le continuous_const hca))
    have ht1S : sInf S ∈ S := hSclosed.csInf_mem hSne hSbdd
    have ht1pos : 0 < sInf S := by
      rcases ht1S.1.lt_or_eq with h | h
      · exact h
      · exfalso; have h2 := ht1S.2.2; rw [← h] at h2; linarith
    have ht1T : sInf S ≤ T := ht1S.2.1
    have hbelow : ∀ s, 0 ≤ s → s < sInf S → a s < aE := by
      intro s hs hst
      by_contra hc; push_neg at hc
      have : sInf S ≤ s := csInf_le hSbdd ⟨hs, by linarith, hc⟩
      linarith
    have hanti1 : AntitoneOn (deriv a) (Set.Icc 0 (sInf S)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (sInf S)) hcd.continuousOn
        (fun s _ => (hdiff₂ s).differentiableWithinAt)
      intro s hs
      rw [interior_Icc] at hs
      have hsI : s ∈ Set.Icc 0 T := ⟨hs.1.le, by linarith [hs.2]⟩
      rw [heq s hsI]
      exact (W2c_EinsteinStaticUniverse_accel_neg G Λ ρ₀ a₀ aE _ hG hρ₀ ha₀ haE hstatic
        (hpos s hsI) (hbelow s hs.1.le hs.2)).le
    have hanti2 : AntitoneOn a (Set.Icc 0 (sInf S)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (sInf S)) hca.continuousOn
        (fun s _ => (hdiff s).differentiableWithinAt)
      intro s hs
      rw [interior_Icc] at hs
      have := hanti1 ⟨le_refl 0, ht1pos.le⟩ ⟨hs.1.le, hs.2.le⟩ hs.1.le
      linarith
    have := hanti2 ⟨le_refl 0, ht1pos.le⟩ ⟨ht1pos.le, le_refl _⟩ ht1pos.le
    linarith [ht1S.2.2]
  have hdd : ∀ s ∈ Set.Icc 0 T, deriv (deriv a) s < 0 := fun s hs => by
    rw [heq s hs]
    exact W2c_EinsteinStaticUniverse_accel_neg G Λ ρ₀ a₀ aE _ hG hρ₀ ha₀ haE hstatic
      (hpos s hs) (key s hs.1 hs.2)
  have hsa1 : StrictAntiOn (deriv a) (Set.Icc 0 T) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 T) hcd.continuousOn
    intro s hs; rw [interior_Icc] at hs; exact hdd s ⟨hs.1.le, hs.2.le⟩
  have hdneg : ∀ s, 0 < s → s ≤ T → deriv a s < 0 := fun s hs hsT =>
    lt_of_lt_of_le (hsa1 ⟨le_refl 0, hT.le⟩ ⟨hs.le, hsT⟩ hs) h₀'
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 T) hca.continuousOn
  intro s hs; rw [interior_Icc] at hs; exact hdneg s hs.1 hs.2.le

theorem W2c_EinsteinStaticUniverse_linearised (G Λ ρ₀ a₀ aE : ℝ) (hG : 0 < G) (hρ₀ : 0 < ρ₀)
    (ha₀ : 0 < a₀) (haE : 0 < aE)
    (hstatic : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) :
    0 < Λ ∧ accel G Λ ρ₀ a₀ aE = 0 ∧ HasDerivAt (accel G Λ ρ₀ a₀) Λ aE ∧
      ∀ t : ℝ, deriv (deriv fun s : ℝ => Real.exp (Real.sqrt Λ * s)) t
        = Λ * Real.exp (Real.sqrt Λ * t) := by
  have hΛpos : 0 < Λ := by rw [hstatic]; unfold dustDensity; positivity
  have h : aE ≠ 0 := haE.ne'
  refine ⟨hΛpos, ?_, ?_, ?_⟩
  · unfold accel; rw [hstatic]; ring
  · have hfun : accel G Λ ρ₀ a₀ = fun x =>
        (-(4 * Real.pi * G / 3) * ρ₀ * a₀ ^ 3) * (x⁻¹ * x⁻¹) + Λ / 3 * x := by
      funext x
      unfold accel dustDensity
      rcases eq_or_ne x 0 with hx | hx
      · simp [hx]
      · field_simp
        try ring
    have hd : HasDerivAt (fun x =>
        (-(4 * Real.pi * G / 3) * ρ₀ * a₀ ^ 3) * (x⁻¹ * x⁻¹) + Λ / 3 * x)
        (-(4 * Real.pi * G / 3) * ρ₀ * a₀ ^ 3 * (-(aE ^ 2)⁻¹ * aE⁻¹ + aE⁻¹ * -(aE ^ 2)⁻¹)
          + Λ / 3 * 1) aE :=
      (((hasDerivAt_inv h).mul (hasDerivAt_inv h)).const_mul
      (-(4 * Real.pi * G / 3) * ρ₀ * a₀ ^ 3)).add ((hasDerivAt_id' aE).const_mul (Λ / 3))
    rw [hfun]
    refine hd.congr_deriv ?_
    rw [hstatic]; unfold dustDensity
    field_simp
    ring
  · intro t
    have hd1 : ∀ s, HasDerivAt (fun s => Real.exp (Real.sqrt Λ * s))
        (Real.exp (Real.sqrt Λ * s) * Real.sqrt Λ) s := by
      intro s
      have := ((hasDerivAt_id' s).const_mul (Real.sqrt Λ)).exp
      simpa using this
    have hd : deriv (fun s => Real.exp (Real.sqrt Λ * s)) =
        fun s => Real.exp (Real.sqrt Λ * s) * Real.sqrt Λ := funext fun s => (hd1 s).deriv
    rw [hd, ((hd1 t).mul_const (Real.sqrt Λ)).deriv, mul_assoc,
      Real.mul_self_sqrt hΛpos.le]
    ring

theorem W2c_EinsteinStaticUniverse_iff (G Λ k ρ₀ a₀ aE : ℝ) (haE : 0 < aE) :
    (FriedmannI G Λ k ρ₀ a₀ (fun _ => aE) Set.univ ∧
        FriedmannII G Λ ρ₀ a₀ (fun _ => aE) Set.univ) ↔
      (Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE ∧ k = Λ * aE ^ 2) := by
  have hd : deriv (fun _ : ℝ => aE) = fun _ => 0 := by funext t; simp
  have hdd : deriv (deriv (fun _ : ℝ => aE)) = fun _ => 0 := by rw [hd]; funext t; simp
  unfold FriedmannI FriedmannII FriedmannGeneral accel
  constructor
  · rintro ⟨h1, h2⟩
    have h1 := h1 0 (Set.mem_univ 0)
    have h2 := h2 0 (Set.mem_univ 0)
    simp only [hdd, hd, deriv_const] at h1 h2
    have h3 : (Λ - 4 * Real.pi * G * dustDensity ρ₀ a₀ aE) * aE = 0 := by
      linear_combination (-3) * h2
    have hΛ : Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE := by
      rcases mul_eq_zero.1 h3 with h | h
      · linarith
      · exact absurd h haE.ne'
    refine ⟨hΛ, ?_⟩
    linear_combination h1 - (2 / 3) * aE ^ 2 * hΛ
  · rintro ⟨hΛ, hk⟩
    refine ⟨fun t _ => ?_, fun t _ => ?_⟩
    · simp only [hdd, hd, deriv_const]
      linear_combination hk + (2 / 3) * aE ^ 2 * hΛ
    · simp only [hdd, hd, deriv_const]
      linear_combination (-aE / 3) * hΛ

theorem W2c_EinsteinStaticUniverse_unstable (G Λ k ρ₀ a₀ aE : ℝ) (hG : 0 < G)
    (hρ₀ : 0 < ρ₀) (ha₀ : 0 < a₀) (haE : 0 < aE) :
    ((FriedmannI G Λ k ρ₀ a₀ (fun _ => aE) Set.univ ∧
        FriedmannII G Λ ρ₀ a₀ (fun _ => aE) Set.univ) ↔
      (Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE ∧ k = Λ * aE ^ 2)) ∧
    (Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE →
      0 < Λ ∧ HasDerivAt (accel G Λ ρ₀ a₀) Λ aE ∧
      (∀ a : ℝ → ℝ, (∀ t : ℝ, DifferentiableAt ℝ a t) →
        (∀ t : ℝ, DifferentiableAt ℝ (deriv a) t) →
        FriedmannII G Λ ρ₀ a₀ a (Set.Ici 0) → aE < a 0 → 0 ≤ deriv a 0 →
        StrictMonoOn a (Set.Ici 0) ∧ Filter.Tendsto a Filter.atTop Filter.atTop) ∧
      (∀ T : ℝ, 0 < T → ∀ a : ℝ → ℝ, (∀ t : ℝ, DifferentiableAt ℝ a t) →
        (∀ t : ℝ, DifferentiableAt ℝ (deriv a) t) →
        (∀ t ∈ Set.Icc 0 T, 0 < a t) → FriedmannII G Λ ρ₀ a₀ a (Set.Icc 0 T) →
        a 0 < aE → deriv a 0 ≤ 0 → StrictAntiOn a (Set.Icc 0 T))) := by
  refine ⟨W2c_EinsteinStaticUniverse_iff G Λ k ρ₀ a₀ aE haE, fun hstatic => ?_⟩
  have hl := W2c_EinsteinStaticUniverse_linearised G Λ ρ₀ a₀ aE hG hρ₀ ha₀ haE hstatic
  refine ⟨hl.1, hl.2.2.1, ?_, ?_⟩
  · intro a h1 h2 h3 h4 h5
    exact W2c_EinsteinStaticUniverse_escape G Λ ρ₀ a₀ aE hG hρ₀ ha₀ haE hstatic a h1 h2 h3 h4 h5
  · intro T hT a h1 h2 h3 h4 h5 h6
    exact W2c_EinsteinStaticUniverse_collapse G Λ ρ₀ a₀ aE T hG hρ₀ ha₀ haE hT hstatic a
      h1 h2 h3 h4 h5 h6

theorem W2c_EinsteinStaticUniverse_accel_eq (G Λ k ρ₀ a₀ : ℝ) (a : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I)
    (hpos : ∀ t ∈ I, 0 < a t) (hne : ∀ t ∈ I, deriv a t ≠ 0)
    (hdiff : ∀ t ∈ I, DifferentiableAt ℝ a t)
    (hdiff₂ : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t)
    (h : FriedmannI G Λ k ρ₀ a₀ a I) :
    FriedmannII G Λ ρ₀ a₀ a I := by
  intro t ht
  have hev : (fun s => deriv a s * deriv a s) =ᶠ[nhds t]
      (fun s => (8 * Real.pi * G / 3 * ρ₀ * a₀ ^ 3) / a s - k + Λ / 3 * (a s * a s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    have h1 := h s hs
    have hs0 := (hpos s hs).ne'
    unfold FriedmannGeneral dustDensity at h1
    rw [← sq, h1]
    field_simp
  have hat := (hdiff t ht).hasDerivAt
  have ha0 := (hpos t ht).ne'
  have hd2 := (hdiff₂ t ht).hasDerivAt
  have hL : HasDerivAt (fun s => deriv a s * deriv a s)
      (deriv (deriv a) t * deriv a t + deriv a t * deriv (deriv a) t) t := hd2.mul hd2
  have hR : HasDerivAt
      (fun s => (8 * Real.pi * G / 3 * ρ₀ * a₀ ^ 3) / a s - k + Λ / 3 * (a s * a s))
      ((0 * a t - 8 * Real.pi * G / 3 * ρ₀ * a₀ ^ 3 * deriv a t) / a t ^ 2 +
        Λ / 3 * (deriv a t * a t + a t * deriv a t)) t :=
    (((hasDerivAt_const t (8 * Real.pi * G / 3 * ρ₀ * a₀ ^ 3)).div hat ha0).sub_const
    k).add ((hat.mul hat).const_mul (Λ / 3))
  have e := hev.deriv_eq
  rw [hL.deriv, hR.deriv] at e
  have e2 : deriv a t * (2 * deriv (deriv a) t + (8 * Real.pi * G / 3 * ρ₀ * a₀ ^ 3) / a t ^ 2
      - 2 * Λ / 3 * a t) = 0 := by
    linear_combination e
  rcases mul_eq_zero.1 e2 with h' | h'
  · exact absurd h' (hne t ht)
  have e3 : deriv (deriv a) t
      = -((8 * Real.pi * G / 3 * ρ₀ * a₀ ^ 3) / a t ^ 2) / 2 + Λ / 3 * a t := by linarith
  rw [e3]
  unfold accel dustDensity
  field_simp
  ring

theorem W2c_EinsteinStaticUniverse_omega (G Λ k ρ₀ a₀ : ℝ) (hG : 0 < G) (a : ℝ → ℝ)
    (I : Set ℝ)
    (h : FriedmannI G Λ k ρ₀ a₀ a I) (t : ℝ) (ht : t ∈ I) (ha : a t ≠ 0)
    (hH : hubbleParameter a t ≠ 0) :
    omegaM G (hubbleParameter a t) (dustDensity ρ₀ a₀ (a t))
        + omegaK k (a t) (hubbleParameter a t)
        + omegaLambda Λ (hubbleParameter a t) = 1 := by
  have h1 := h t ht
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hG' : G ≠ 0 := hG.ne'
  have hX : a t ^ 2 * hubbleParameter a t ^ 2 = deriv a t ^ 2 := by
    unfold hubbleParameter; field_simp
    try ring
  have hX0 : a t ^ 2 * hubbleParameter a t ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hH)
  have key : omegaM G (hubbleParameter a t) (dustDensity ρ₀ a₀ (a t))
        + omegaK k (a t) (hubbleParameter a t)
        + omegaLambda Λ (hubbleParameter a t) =
      (8 * Real.pi * G / 3 * dustDensity ρ₀ a₀ (a t) * a t ^ 2 - k + Λ / 3 * a t ^ 2) /
        (a t ^ 2 * hubbleParameter a t ^ 2) := by
    unfold omegaM criticalDensity omegaK omegaLambda
    field_simp
    ring
  rw [key]
  unfold FriedmannGeneral at h1
  rw [← h1, ← hX]
  exact div_self hX0

theorem W2c_EinsteinStaticUniverse_vacuum_energy (G Λ k : ℝ) (hG : G ≠ 0) (ρ : ℝ → ℝ)
    (a : ℝ → ℝ) (I : Set ℝ) :
    (FriedmannGeneral G Λ k ρ a I ↔
      FriedmannGeneral G 0 k (fun t => ρ t + vacuumDensity G Λ) a I) ∧
    ContinuityEquation (fun _ => vacuumDensity G Λ) (fun _ => vacuumPressure G Λ) a I := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · unfold FriedmannGeneral vacuumDensity
    constructor
    · intro h t ht; rw [h t ht]; field_simp; try ring
    · intro h t ht; rw [h t ht]; field_simp; try ring
  · intro t ht
    unfold vacuumDensity vacuumPressure
    simp

theorem solution (G Λ k : ℝ) (hG : G ≠ 0) (ρ : ℝ → ℝ) (a : ℝ → ℝ) (I : Set ℝ) :
    (FriedmannGeneral G Λ k ρ a I ↔
      FriedmannGeneral G 0 k (fun t => ρ t + vacuumDensity G Λ) a I) ∧
    ContinuityEquation (fun _ => vacuumDensity G Λ) (fun _ => vacuumPressure G Λ) a I := by
  apply W2c_EinsteinStaticUniverse_vacuum_energy <;> assumption
