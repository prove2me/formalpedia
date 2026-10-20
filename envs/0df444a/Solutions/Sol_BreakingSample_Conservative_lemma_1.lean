-- Prove2me | solution 1 for BreakingSample.Conservative.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T03:32:56.557705+00:00
-- url     : https://prove2.me/submissions/e0511d19-ebf0-41af-8bfe-ec9fb82809dc

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling

set_option autoImplicit false

open Matrix

theorem bs1_mp {S : Type} [Fintype S] (M : Matrix S S ℝ) (hM0 : ∀ s s', 0 ≤ M s s')
    (hM1 : ∀ s, ∑ s', M s s' = 1) (γ c : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (y : S → ℝ)
    (h : ∀ s, y s ≤ c + γ * ∑ s', M s s' * y s') : ∀ s, y s ≤ c / (1 - γ) := by
  intro s
  have : Nonempty S := ⟨s⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max y
  have hsum : ∑ s', M s0 s' * y s' ≤ y s0 := by
    calc ∑ s', M s0 s' * y s' ≤ ∑ s', M s0 s' * y s0 :=
          Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hs0 s') (hM0 s0 s'))
      _ = y s0 := by rw [← Finset.sum_mul, hM1, one_mul]
  have h1 := h s0
  have h2 : y s0 * (1 - γ) ≤ c := by nlinarith
  calc y s ≤ y s0 := hs0 s
    _ ≤ c / (1 - γ) := by rw [le_div_iff₀ (by linarith)]; exact h2

theorem bs1_lin {S : Type} [Fintype S] (m f g h : S → ℝ) (a b c : ℝ) :
    ∑ s, m s * (a * f s + b * g s + c * h s)
      = a * ∑ s, m s * f s + b * ∑ s, m s * g s + c * ∑ s, m s * h s := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => by ring)

theorem bs1_jensen {S : Type} [Fintype S] (m : S → ℝ) (hm0 : ∀ s, 0 ≤ m s) (hm1 : ∑ s, m s = 1)
    (y : S → ℝ) : (∑ s, m s * y s) ^ 2 ≤ ∑ s, m s * y s ^ 2 := by
  have h : 0 ≤ ∑ s, m s * (y s - ∑ t, m t * y t) ^ 2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hm0 s) (sq_nonneg _))
  have e : ∑ s, m s * (y s - ∑ t, m t * y t) ^ 2
      = 1 * ∑ s, m s * y s ^ 2 + (-2 * ∑ t, m t * y t) * ∑ s, m s * y s
        + (∑ t, m t * y t) ^ 2 * ∑ s, m s * (fun _ => (1 : ℝ)) s := by
    rw [← bs1_lin]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have e1 : ∑ s, m s * (fun _ => (1 : ℝ)) s = 1 := by simpa using hm1
  rw [e, e1] at h
  nlinarith

theorem bs1_mulVec {S : Type} [Fintype S] [DecidableEq S] (M : Matrix S S ℝ) (γ : ℝ)
    (u : S → ℝ) (s : S) : ((1 - γ • M) *ᵥ u) s = u s - γ * ∑ s', M s s' * u s' := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => sub_mul _ _ _), Finset.sum_sub_distrib, Finset.mul_sum]
  simp [Matrix.one_apply, mul_assoc]

theorem bs1_unit {S : Type} [Fintype S] [DecidableEq S] (M : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) : IsUnit (1 - γ • M) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have hd : ∀ s, (v - w) s = 0 + γ * ∑ s', M s s' * (v - w) s' := by
    intro s
    have h1 := congrFun hvw s
    rw [bs1_mulVec, bs1_mulVec] at h1
    have : ∑ s', M s s' * (v - w) s' = ∑ s', M s s' * v s' - ∑ s', M s s' * w s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s' _ => by simp [mul_sub])
    rw [this]; simp only [Pi.sub_apply]; linarith
  have hd' : ∀ s, (-(v - w)) s = 0 + γ * ∑ s', M s s' * (-(v - w)) s' := by
    intro s
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [hd s]; ring
  have a1 := bs1_mp M hM0 hM1 γ 0 hγ0 hγ1 (v - w) (fun s => (hd s).le)
  have a2 := bs1_mp M hM0 hM1 γ 0 hγ0 hγ1 (-(v - w)) (fun s => (hd' s).le)
  funext s
  have b1 := a1 s
  have b2 := a2 s
  simp only [zero_div, Pi.sub_apply, Pi.neg_apply] at b1 b2
  linarith

theorem bs1_res_fix {S : Type} [Fintype S] [DecidableEq S] (M : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (w : S → ℝ) (s : S) :
    ((1 - γ • M)⁻¹ *ᵥ w) s = w s + γ * ∑ s', M s s' * ((1 - γ • M)⁻¹ *ᵥ w) s' := by
  have hU := bs1_unit M hM0 hM1 γ hγ0 hγ1
  have h : (1 - γ • M) *ᵥ ((1 - γ • M)⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
  have h2 := congrFun h s
  rw [bs1_mulVec] at h2
  linarith

theorem bs1_res_unique {S : Type} [Fintype S] [DecidableEq S] (M : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (w y : S → ℝ) (hy : ∀ s, y s = w s + γ * ∑ s', M s s' * y s') :
    (1 - γ • M)⁻¹ *ᵥ w = y := by
  have hU := bs1_unit M hM0 hM1 γ hγ0 hγ1
  have h1 : (1 - γ • M) *ᵥ y = w := by
    funext s; rw [bs1_mulVec]; linarith [hy s]
  rw [← h1, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]

theorem bs1_nonneg {S : Type} [Fintype S] (M : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (u Z : S → ℝ) (hu : ∀ s, 0 ≤ u s)
    (hZ : ∀ s, Z s = u s + γ * ∑ s', M s s' * Z s') : ∀ s, 0 ≤ Z s := by
  have h := bs1_mp M hM0 hM1 γ 0 hγ0 hγ1 (fun s => -Z s) (fun s => by
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [hZ s]; linarith [hu s])
  intro s
  have := h s
  simp only [zero_div] at this
  linarith

theorem bs1_upper {S : Type} [Fintype S] (M : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (u Z : S → ℝ) (C : ℝ) (hu : ∀ s, u s ≤ C)
    (hZ : ∀ s, Z s = u s + γ * ∑ s', M s s' * Z s') : ∀ s, Z s ≤ C / (1 - γ) :=
  bs1_mp M hM0 hM1 γ C hγ0 hγ1 Z (fun s => by rw [hZ s] at *; linarith [hu s])

/-- one comparison step of the recursion -/
theorem bs1_step {S : Type} [Fintype S] (M Mh : Matrix S S ℝ)
    (hMh0 : ∀ s s', 0 ≤ Mh s s') (hMh1 : ∀ s, ∑ s', Mh s s' = 1) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (w u Vh V Z : S → ℝ) (α β x : ℝ)
    (hVh : ∀ s, Vh s = w s + γ * ∑ s', Mh s s' * Vh s')
    (hV : ∀ s, V s = w s + γ * ∑ s', M s s' * V s')
    (hZ : ∀ s, Z s = u s + γ * ∑ s', Mh s s' * Z s')
    (hB : ∀ s, |∑ s', Mh s s' * V s' - ∑ s', M s s' * V s'| ≤ α * u s + β * x) :
    ∀ s, |Vh s - V s| ≤ γ * α * Z s + γ * β * x / (1 - γ) := by
  have h1γ : 0 < 1 - γ := by linarith
  set c := γ * β * x / (1 - γ) with hc
  have hc' : c * (1 - γ) = γ * β * x := by rw [hc]; field_simp
  have one : ∀ s, ∑ s', Mh s s' * (fun _ => (1 : ℝ)) s' = 1 := fun s => by simpa using hMh1 s
  have key : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) → ∀ s,
      σ * (Vh s - V s) - γ * α * Z s - c ≤ 0 / (1 - γ) := by
    intro σ hσ
    have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> simp [h]
    apply bs1_mp Mh hMh0 hMh1 γ 0 hγ0 hγ1 (fun s => σ * (Vh s - V s) - γ * α * Z s - c)
    intro s
    have e : ∑ s', Mh s s' * (σ * (Vh s' - V s') - γ * α * Z s' - c)
        = σ * ∑ s', Mh s s' * (Vh s' - V s') + (-(γ * α)) * ∑ s', Mh s s' * Z s'
          + (-c) * ∑ s', Mh s s' * (fun _ => (1 : ℝ)) s' := by
      rw [← bs1_lin]; exact Finset.sum_congr rfl (fun s' _ => by ring)
    have e2 : ∑ s', Mh s s' * (Vh s' - V s')
        = ∑ s', Mh s s' * Vh s' - ∑ s', Mh s s' * V s' := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun s' _ => by ring)
    rw [e, one s, e2]
    have hb := hB s
    have hb' : σ * (∑ s', Mh s s' * V s' - ∑ s', M s s' * V s') ≤ α * u s + β * x := by
      rcases hσ with h | h <;> subst h
      · linarith [le_abs_self (∑ s', Mh s s' * V s' - ∑ s', M s s' * V s')]
      · linarith [neg_abs_le (∑ s', Mh s s' * V s' - ∑ s', M s s' * V s')]
    rw [hVh s, hV s, hZ s]
    nlinarith
  intro s
  have k1 := key 1 (Or.inl rfl) s
  have k2 := key (-1) (Or.inr rfl) s
  simp only [zero_div] at k1 k2
  rw [abs_le]; constructor <;> linarith

/-- the variance lemma, squared form -/
theorem bs1_var {S : Type} [Fintype S] [DecidableEq S] (M : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1) (γ : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (w V Y : S → ℝ) (B : ℝ) (hw : ∀ s, 0 ≤ w s)
    (hV : ∀ s, V s = w s + γ * ∑ s', M s s' * V s') (hV0 : ∀ s, 0 ≤ V s) (hVB : ∀ s, V s ≤ B)
    (hY : ∀ s, Y s = Real.sqrt (∑ s', M s s' * V s' ^ 2 - (∑ s', M s s' * V s') ^ 2)
      + γ * ∑ s', M s s' * Y s') :
    ∀ s, Y s ^ 2 ≤ 2 * B ^ 2 / (γ ^ 2 * (1 - γ)) := by
  have h1γ : 0 < 1 - γ := by linarith
  set v : S → ℝ := fun s => ∑ s', M s s' * V s' ^ 2 - (∑ s', M s s' * V s') ^ 2 with hv
  have hv0 : ∀ s, 0 ≤ v s := fun s => by
    have := bs1_jensen (M s) (hM0 s) (hM1 s) V
    simp only [hv]; linarith
  set U := (1 - γ • M)⁻¹ *ᵥ v with hUdef
  have hU : ∀ s, U s = v s + γ * ∑ s', M s s' * U s' :=
    fun s => bs1_res_fix M hM0 hM1 γ hγ0.le hγ1 v s
  have one : ∀ s, ∑ s', M s s' * (fun _ => (1 : ℝ)) s' = 1 := fun s => by simpa using hM1 s
  -- (a) γ²U ≤ 2 B V - γ V²
  have ha := bs1_mp M hM0 hM1 γ 0 hγ0.le hγ1
    (fun s => γ ^ 2 * U s + γ * V s ^ 2 - 2 * B * V s) (by
      intro s
      have e : ∑ s', M s s' * (γ ^ 2 * U s' + γ * V s' ^ 2 - 2 * B * V s')
          = γ ^ 2 * ∑ s', M s s' * U s' + γ * ∑ s', M s s' * V s' ^ 2
            + (-2 * B) * ∑ s', M s s' * V s' := by
        rw [← bs1_lin]; exact Finset.sum_congr rfl (fun s' _ => by ring)
      rw [e]
      have hUs := hU s
      have hVs := hV s
      have hvs : v s = ∑ s', M s s' * V s' ^ 2 - (∑ s', M s s' * V s') ^ 2 := rfl
      have hB' := hVB s
      have hw' := hw s
      have hV0' := hV0 s
      have hpv : γ * ∑ s', M s s' * V s' = V s - w s := by linarith
      have : γ ^ 2 * (∑ s', M s s' * V s') ^ 2 = (V s - w s) ^ 2 := by rw [← hpv]; ring
      nlinarith [mul_nonneg hw' (sub_nonneg.mpr hB'), sq_nonneg (V s), sq_nonneg (w s)])
  -- (b) Y² ≤ U/(1-γ)
  have hb := bs1_mp M hM0 hM1 γ 0 hγ0.le hγ1 (fun s => Y s ^ 2 - U s / (1 - γ)) (by
      intro s
      have e : ∑ s', M s s' * (Y s' ^ 2 - U s' / (1 - γ))
          = 1 * ∑ s', M s s' * Y s' ^ 2 + (-(1 / (1 - γ))) * ∑ s', M s s' * U s'
            + 0 * ∑ s', M s s' * (fun _ => (1 : ℝ)) s' := by
        rw [← bs1_lin]; exact Finset.sum_congr rfl (fun s' _ => by ring)
      rw [e]
      have hj := bs1_jensen (M s) (hM0 s) (hM1 s) Y
      have hsq : Real.sqrt (v s) ^ 2 = v s := Real.sq_sqrt (hv0 s)
      have hYs : Y s = Real.sqrt (v s) + γ * ∑ s', M s s' * Y s' := hY s
      have hUs := hU s
      set p := Real.sqrt (v s)
      set q := ∑ s', M s s' * Y s'
      have hconv : (p + γ * q) ^ 2 * (1 - γ) ≤ p ^ 2 + γ * (1 - γ) * q ^ 2 := by
        nlinarith [mul_nonneg hγ0.le (sq_nonneg (p - (1 - γ) * q))]
      have hY2 : Y s ^ 2 ≤ v s / (1 - γ) + γ * q ^ 2 := by
        rw [hYs, ← hsq, div_add' _ _ _ h1γ.ne', le_div_iff₀ h1γ]; nlinarith
      have hU2 : U s / (1 - γ) = v s / (1 - γ) + γ * ((∑ s', M s s' * U s') / (1 - γ)) := by
        rw [hUs]; field_simp
      rw [hU2]
      have : γ * q ^ 2 ≤ γ * ∑ s', M s s' * Y s' ^ 2 := mul_le_mul_of_nonneg_left hj hγ0.le
      have e3 : (1 : ℝ) * ∑ s', M s s' * Y s' ^ 2 + -(1 / (1 - γ)) * ∑ s', M s s' * U s' + 0 * 1
          = ∑ s', M s s' * Y s' ^ 2 - (∑ s', M s s' * U s') / (1 - γ) := by ring
      rw [one s, e3]
      nlinarith)
  intro s
  have a1 := ha s
  have b1 := hb s
  simp only [zero_div] at a1 b1
  have hB0 : 0 ≤ B := le_trans (hV0 s) (hVB s)
  have hU2 : γ ^ 2 * U s ≤ 2 * B ^ 2 := by
    nlinarith [hV0 s, hVB s, mul_le_mul_of_nonneg_left (hVB s) hB0, sq_nonneg (V s)]
  have hU3 : U s ≤ 2 * B ^ 2 / γ ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  calc Y s ^ 2 ≤ U s / (1 - γ) := by linarith
    _ ≤ 2 * B ^ 2 / γ ^ 2 / (1 - γ) := div_le_div_of_nonneg_right hU3 h1γ.le
    _ = 2 * B ^ 2 / (γ ^ 2 * (1 - γ)) := by rw [div_div]

-- ===== Part B: RL glue =====

open FoundationsML.ReinforcementLearning in
theorem bs1_D_prob {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1) (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · show 0 ≤ (if s = s0 then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · show ∑ s, (if s = s0 then (1 : ℝ) else 0) = 1
      simp
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · show 0 ≤ ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s'
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (hT0 s s'))
    · show ∑ s', ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hT1, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem bs1_D_front {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) :
    ∀ (s0 u : S), OccupationDist π P s0 (t + 1) u =
      ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t u := by
  induction t with
  | zero =>
    intro s0 u
    show ∑ s, (if s = s0 then (1 : ℝ) else 0) * InducedTransition π P s u =
      ∑ s', InducedTransition π P s0 s' * (if u = s' then (1 : ℝ) else 0)
    simp
  | succ t ih =>
    intro s0 u
    calc OccupationDist π P s0 (t + 1 + 1) u
        = ∑ v, (∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t v) *
            InducedTransition π P v u := by
          show ∑ v, OccupationDist π P s0 (t + 1) v * InducedTransition π P v u = _
          exact Finset.sum_congr rfl (fun v _ => by rw [ih s0 v])
      _ = ∑ s', InducedTransition π P s0 s' *
            ∑ v, OccupationDist π P s' t v * InducedTransition π P v u := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      _ = ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' (t + 1) u := rfl

open FoundationsML.ReinforcementLearning in
theorem bs1_summable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := bs1_D_prob π P hT0 hT1 s0 t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
  calc |∑ s', OccupationDist π P s0 t s' * g s'|
      ≤ ∑ s', |OccupationDist π P s0 t s' * g s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |g s'| := by
      apply Finset.sum_le_sum
      intro s' _
      rw [abs_mul, abs_of_nonneg (hnn s')]
      have h1 : OccupationDist π P s0 t s' ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s')
      calc OccupationDist π P s0 t s' * |g s'| ≤ 1 * |g s'| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |g s'| := one_mul _

open FoundationsML.ReinforcementLearning in
theorem bs1_bellman_gen {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ)
    (hT0 : ∀ s s', 0 ≤ InducedTransition π P s s')
    (hT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by
  have hsum := fun s0 => bs1_summable π P hT0 hT1 γ hγ0 hγ1 (InducedReward π Er) s0
  have key : ∀ t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist π P s (t + 1) u * InducedReward π Er u =
      γ * ∑ s', InducedTransition π P s s' *
        (γ ^ t * ∑ u, OccupationDist π P s' t u * InducedReward π Er u) := by
    intro t
    simp_rw [bs1_D_front π P t s]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  unfold PolicyValue
  rw [(hsum s).tsum_eq_zero_add, tsum_congr key, tsum_mul_left,
    Summable.tsum_finsetSum (fun s' _ => (hsum s').mul_left (InducedTransition π P s s'))]
  simp_rw [tsum_mul_left]
  have h0 : γ ^ 0 * ∑ u, OccupationDist π P s 0 u * InducedReward π Er u = InducedReward π Er s := by
    show γ ^ 0 * ∑ u, (if u = s then (1 : ℝ) else 0) * InducedReward π Er u = _
    simp
  rw [h0]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_it_det {S A : Type} [Fintype A] [DecidableEq A] (π : S → A) (P : S → A → S → ℝ)
    (s s' : S) : InducedTransition (detPolicy π) P s s' = P s (π s) s' := by
  simp [InducedTransition, detPolicy]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_ir_det {S A : Type} [Fintype A] [DecidableEq A] (π : S → A) (r : S → A → ℝ)
    (s : S) : InducedReward (detPolicy π) r s = r s (π s) := by
  simp [InducedReward, detPolicy]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_value_bellman {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A) (s : S) :
    value P r γ π s = policyReward r π s
      + γ * ∑ s', policyMatrix P π s s' * value P r γ π s' := by
  unfold value
  rw [bs1_bellman_gen (detPolicy π) P (fun s s' => by rw [bs1_it_det]; exact (hP s (π s)).1 s')
    (fun s => by simp_rw [bs1_it_det]; exact (hP s (π s)).2) r γ hγ0 hγ1 s]
  simp only [bs1_it_det, bs1_ir_det, policyReward, policyMatrix]

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_value_res {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A) :
    resolvent P γ π *ᵥ policyReward r π = fun s => value P r γ π s :=
  bs1_res_unique (policyMatrix P π) (fun s s' => (hP s (π s)).1 s') (fun s => (hP s (π s)).2)
    γ hγ0 hγ1 (policyReward r π) _ (bs1_value_bellman P hP r γ hγ0 hγ1 π)

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_aux_fix {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A) (l : ℕ) (s : S) :
    auxV P r γ π (l + 1) s = Real.sqrt (varPi P π (auxV P r γ π l) s)
      + γ * ∑ s', policyMatrix P π s s' * auxV P r γ π (l + 1) s' :=
  bs1_res_fix (policyMatrix P π) (fun s s' => (hP s (π s)).1 s') (fun s => (hP s (π s)).2)
    γ hγ0 hγ1 _ s

open FoundationsML.ReinforcementLearning BreakingSample.Perturbed in
theorem bs1_aux_zero {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A) :
    auxV P r γ π 0 = fun s => value P r γ π s :=
  bs1_value_res P hP r γ hγ0 hγ1 π

-- ===== Part D: the deterministic recursion =====

theorem bs1_norm_le {S : Type} [Fintype S] (f : S → ℝ) (s : S) : f s ≤ ‖f‖ :=
  le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using norm_le_pi_norm f s)

theorem bs1_det {S : Type} [Fintype S] [DecidableEq S] (M Mh : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1)
    (hMh0 : ∀ s s', 0 ≤ Mh s s') (hMh1 : ∀ s, ∑ s', Mh s s' = 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (V w : ℕ → S → ℝ) (Vh : S → ℝ)
    (hV : ∀ l s, V l s = w l s + γ * ∑ s', M s s' * V l s')
    (hw0 : ∀ s, 0 ≤ w 0 s)
    (hwS : ∀ l s, w (l + 1) s = Real.sqrt (∑ s', M s s' * V l s' ^ 2 - (∑ s', M s s' * V l s') ^ 2))
    (hVh : ∀ s, Vh s = w 0 s + γ * ∑ s', Mh s s' * Vh s')
    (α β ρ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 = 2 * α ^ 2 / (1 - γ))
    (m : ℕ) (hm : 1 ≤ m)
    (hn2 : ρ * (1 + γ * β / (1 - γ) + 1 / 4) ≤ 1 / 4)
    (hn3 : ρ ^ (m - 1) * (γ * α / (1 - γ)) ≤ 1 / 4)
    (hE : ∀ l, l ≤ m → ∀ s, |∑ s', Mh s s' * V l s' - ∑ s', M s s' * V l s'|
        ≤ α * w (l + 1) s + β * ‖V l‖) :
    ∀ s, |Vh s - V 0 s| ≤ γ * α * (3 / 2 + γ * β / (1 - γ)) * ‖V 1‖ + γ * β * ‖V 0‖ / (1 - γ) := by
  have h1γ : 0 < 1 - γ := by linarith
  -- nonnegativity of V and w
  have hwnn : ∀ l s, 0 ≤ w l s := by
    intro l s; cases l with
    | zero => exact hw0 s
    | succ l => rw [hwS]; exact Real.sqrt_nonneg _
  have hVnn : ∀ l s, 0 ≤ V l s := fun l =>
    bs1_nonneg M hM0 hM1 γ hγ0.le hγ1 (w l) (V l) (hwnn l) (hV l)
  set x : ℕ → ℝ := fun l => ‖V l‖ with hx
  have hx0 : ∀ l, 0 ≤ x l := fun l => norm_nonneg _
  have hVx : ∀ l s, V l s ≤ x l := fun l s => bs1_norm_le (V l) s
  -- w (l+1) ≤ x l
  have hwx : ∀ l s, w (l + 1) s ≤ x l := by
    intro l s
    rw [hwS]
    have hj := bs1_jensen (M s) (hM0 s) (hM1 s) (V l)
    have h2 : ∑ s', M s s' * V l s' ^ 2 ≤ x l ^ 2 := by
      calc ∑ s', M s s' * V l s' ^ 2 ≤ ∑ s', M s s' * x l ^ 2 :=
            Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (hVnn l s') (hVx l s') 2) (hM0 s s'))
        _ = x l ^ 2 := by rw [← Finset.sum_mul, hM1, one_mul]
    calc Real.sqrt (∑ s', M s s' * V l s' ^ 2 - (∑ s', M s s' * V l s') ^ 2)
        ≤ Real.sqrt (x l ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (∑ s', M s s' * V l s')])
      _ = x l := Real.sqrt_sq (hx0 l)
  -- variance lemma in norm form: (γ α x (l+1)) ≤ ρ x l
  have hvar : ∀ l, γ * α * x (l + 1) ≤ ρ * x l := by
    intro l
    have hv := bs1_var M hM0 hM1 γ hγ0 hγ1 (w l) (V l) (V (l + 1)) (x l) (hwnn l) (hV l)
      (hVnn l) (hVx l) (fun s => by rw [hV (l + 1) s, hwS])
    have hK : 0 ≤ 2 * x l ^ 2 / (γ ^ 2 * (1 - γ)) := by positivity
    have hxn : x (l + 1) ≤ Real.sqrt (2 * x l ^ 2 / (γ ^ 2 * (1 - γ))) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro s
      rw [Real.norm_eq_abs, abs_of_nonneg (hVnn (l + 1) s)]
      exact Real.le_sqrt_of_sq_le (hv s)
    have hsq : x (l + 1) ^ 2 ≤ 2 * x l ^ 2 / (γ ^ 2 * (1 - γ)) := by
      have := pow_le_pow_left₀ (hx0 _) hxn 2
      rwa [Real.sq_sqrt hK] at this
    have h3 : (γ * α * x (l + 1)) ^ 2 ≤ (ρ * x l) ^ 2 := by
      calc (γ * α * x (l + 1)) ^ 2 = (γ * α) ^ 2 * x (l + 1) ^ 2 := by ring
        _ ≤ (γ * α) ^ 2 * (2 * x l ^ 2 / (γ ^ 2 * (1 - γ))) :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (ρ * x l) ^ 2 := by
            rw [mul_pow ρ (x l) 2, hρ]; first | (field_simp; ring) | field_simp
    have hα0 : 0 ≤ γ * α * x (l + 1) := mul_nonneg (mul_nonneg hγ0.le hα) (hx0 _)
    exact (pow_le_pow_iff_left₀ hα0 (mul_nonneg hρ0 (hx0 l)) two_ne_zero).mp h3
  -- the empirical resolvent vectors Z l = Rhat w (l+1)
  set Z : ℕ → S → ℝ := fun l => (1 - γ • Mh)⁻¹ *ᵥ w (l + 1) with hZdef
  have hZ : ∀ l s, Z l s = w (l + 1) s + γ * ∑ s', Mh s s' * Z l s' :=
    fun l s => bs1_res_fix Mh hMh0 hMh1 γ hγ0.le hγ1 (w (l + 1)) s
  have hZnn : ∀ l s, 0 ≤ Z l s := fun l =>
    bs1_nonneg Mh hMh0 hMh1 γ hγ0.le hγ1 (w (l + 1)) (Z l) (hwnn (l + 1)) (hZ l)
  set T : ℕ → ℝ := fun l => ‖Z l‖ with hT
  have hT0 : ∀ l, 0 ≤ T l := fun l => norm_nonneg _
  have hZT : ∀ l s, Z l s ≤ T l := fun l s => bs1_norm_le (Z l) s
  set b2 := γ * β / (1 - γ) with hb2
  have hb20 : 0 ≤ b2 := by positivity
  -- claim B: T l ≤ (1 + b2) x (l+1) + γ α T (l+1) for l < m
  have hB : ∀ l, l < m → T l ≤ (1 + b2) * x (l + 1) + γ * α * T (l + 1) := by
    intro l hl
    have hs := bs1_step M Mh hMh0 hMh1 γ hγ0.le hγ1 (w (l + 1)) (w (l + 2)) (Z l) (V (l + 1))
      (Z (l + 1)) α β (x (l + 1)) (hZ l) (hV (l + 1)) (hZ (l + 1)) (hE (l + 1) hl)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hZnn l s)]
    have h1 := (abs_le.mp (hs s)).2
    have h2 := hVx (l + 1) s
    have h3 : γ * α * Z (l + 1) s ≤ γ * α * T (l + 1) :=
      mul_le_mul_of_nonneg_left (hZT _ s) (by positivity)
    have e : γ * β * x (l + 1) / (1 - γ) = b2 * x (l + 1) := by rw [hb2]; ring
    linarith
  -- claim C: T m ≤ x m / (1 - γ)
  have hC : T m ≤ x m / (1 - γ) := by
    have hu := bs1_upper Mh hMh0 hMh1 γ hγ0.le hγ1 (w (m + 1)) (Z m) (x m) (hwx m) (hZ m)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hZnn m s)]
    exact hu s
  -- downward induction
  set c := γ * α with hc
  have hc0 : 0 ≤ c := by positivity
  set θ := γ * α / (1 - γ) with hθ
  have hind : ∀ j k, k + j = m → 1 ≤ k → c * T k ≤ (1 / 4 + ρ ^ j * θ) * x k := by
    intro j
    induction j with
    | zero =>
      intro k hk _
      simp only [add_zero] at hk
      subst hk
      have : c * T k ≤ c * (x k / (1 - γ)) := mul_le_mul_of_nonneg_left hC hc0
      have e : c * (x k / (1 - γ)) = θ * x k := by rw [hθ, hc]; ring
      have : 0 ≤ 1 / 4 * x k := by positivity
      simp only [pow_zero, one_mul]
      nlinarith
    | succ j ih =>
      intro k hk hk1
      have ih' := ih (k + 1) (by omega) (by omega)
      have hBk := hB k (by omega)
      have hv := hvar k
      have hθ0 : 0 ≤ θ := by positivity
      have hρj : 0 ≤ ρ ^ j * θ := mul_nonneg (pow_nonneg hρ0 j) hθ0
      calc c * T k ≤ c * ((1 + b2) * x (k + 1) + c * T (k + 1)) :=
            mul_le_mul_of_nonneg_left hBk hc0
        _ = (1 + b2) * (c * x (k + 1)) + c * (c * T (k + 1)) := by ring
        _ ≤ (1 + b2) * (ρ * x k) + c * ((1 / 4 + ρ ^ j * θ) * x (k + 1)) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hv (by positivity)
            · exact mul_le_mul_of_nonneg_left ih' hc0
        _ = (1 + b2) * (ρ * x k) + (1 / 4 + ρ ^ j * θ) * (c * x (k + 1)) := by ring
        _ ≤ (1 + b2) * (ρ * x k) + (1 / 4 + ρ ^ j * θ) * (ρ * x k) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (by positivity))
        _ = ρ * (1 + b2 + 1 / 4) * x k + ρ ^ (j + 1) * θ * x k := by ring
        _ ≤ 1 / 4 * x k + ρ ^ (j + 1) * θ * x k := by
            have := mul_le_mul_of_nonneg_right hn2 (hx0 k)
            linarith
        _ = (1 / 4 + ρ ^ (j + 1) * θ) * x k := by ring
  have hT1 : c * T 1 ≤ 1 / 2 * x 1 := by
    have := hind (m - 1) 1 (by omega) le_rfl
    have h5 : (1 / 4 + ρ ^ (m - 1) * θ) * x 1 ≤ (1 / 2) * x 1 :=
      mul_le_mul_of_nonneg_right (by linarith) (hx0 1)
    linarith
  have hT0' : T 0 ≤ (3 / 2 + b2) * x 1 := by
    have := hB 0 (by omega)
    linarith
  -- claim A
  have hA := bs1_step M Mh hMh0 hMh1 γ hγ0.le hγ1 (w 0) (w 1) Vh (V 0) (Z 0) α β (x 0)
    hVh (hV 0) (hZ 0) (hE 0 (Nat.zero_le _))
  intro s
  have h1 := hA s
  have h2 : γ * α * Z 0 s ≤ γ * α * ((3 / 2 + b2) * x 1) :=
    mul_le_mul_of_nonneg_left ((hZT 0 s).trans hT0') hc0
  calc |Vh s - V 0 s| ≤ γ * α * Z 0 s + γ * β * x 0 / (1 - γ) := h1
    _ ≤ γ * α * ((3 / 2 + b2) * x 1) + γ * β * x 0 / (1 - γ) := by linarith
    _ = γ * α * (3 / 2 + γ * β / (1 - γ)) * ‖V 1‖ + γ * β * ‖V 0‖ / (1 - γ) := by
        rw [hb2]; ring

-- ===== Part C: Bernstein =====

open BreakingSample.Perturbed in
theorem bs1_factor {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (N : ℕ)
    (g : S → A → Fin N → S → ℝ) :
    ∑ x : Samples S A N, ∏ s, ∏ a, ∏ i, g s a i (x s a i)
      = ∏ s, ∏ a, ∏ i, ∑ s', g s a i s' := by
  simp only [Fintype.prod_sum]

open BreakingSample.Perturbed in
theorem bs1_emp_sum {S A : Type} [Fintype S] [DecidableEq S] {N : ℕ} (x : Samples S A N)
    (s : S) (a : A) (f : S → ℝ) :
    ∑ s', empKernel x s a s' * f s' = (∑ i, f (x s a i)) / N := by
  unfold empKernel
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [ite_mul, Finset.sum_ite_eq]

open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_emp_kernel {S A : Type} [Fintype S] [DecidableEq S] {N : ℕ} (hN : 0 < N)
    (x : Samples S A N) : IsTransitionKernel (empKernel x) := by
  intro s a
  refine ⟨fun s' => ?_, ?_⟩
  · unfold empKernel; positivity
  · have h := bs1_emp_sum x s a (fun _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [h]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp

open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_weight_nonneg {S A : Type} [Fintype S] [Fintype A] {N : ℕ}
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (x : Samples S A N) :
    0 ≤ sampleWeight P x := by
  unfold sampleWeight
  exact Finset.prod_nonneg (fun s _ => Finset.prod_nonneg (fun a _ =>
    Finset.prod_nonneg (fun i _ => (hP s a).1 _)))

open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_mgf_prod {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (N : ℕ) (s0 : S) (a0 : A) (h : S → ℝ) :
    ∑ x : Samples S A N, sampleWeight P x * ∏ i, h (x s0 a0 i)
      = (∑ s', P s0 a0 s' * h s') ^ N := by
  have e : ∀ x : Samples S A N, sampleWeight P x * ∏ i, h (x s0 a0 i)
      = ∏ s, ∏ a, ∏ i, (P s a (x s a i) * (if s = s0 ∧ a = a0 then h (x s a i) else 1)) := by
    intro x
    unfold sampleWeight
    simp only [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single s0, Finset.prod_eq_single a0]
    · simp
    · intro a _ ha; simp [ha]
    · simp
    · intro s _ hs; simp [hs]
    · simp
  have hf := bs1_factor N (fun s a _ s' => P s a s' * (if s = s0 ∧ a = a0 then h s' else 1))
  rw [Finset.sum_congr rfl (fun x _ => e x), hf]
  have e2 : ∀ (s : S) (a : A), ∑ s', P s a s' * (if s = s0 ∧ a = a0 then h s' else 1)
      = if s = s0 ∧ a = a0 then ∑ s', P s0 a0 s' * h s' else 1 := by
    intro s a
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; rfl
    · simp [(hP s a).2]
  simp_rw [e2]
  rw [Finset.prod_eq_single s0, Finset.prod_eq_single a0]
  · simp
  · intro a _ ha; simp [ha]
  · simp
  · intro s _ hs; simp [hs]
  · simp

theorem bs1_mgf_one {S : Type} [Fintype S] (m : S → ℝ) (hm0 : ∀ s, 0 ≤ m s)
    (hm1 : ∑ s, m s = 1) (f : S → ℝ) (lam : ℝ)
    (hb : ∀ s, |lam * (f s - ∑ t, m t * f t)| ≤ 1) :
    ∑ s, m s * Real.exp (lam * (f s - ∑ t, m t * f t))
      ≤ Real.exp (lam ^ 2 * (∑ s, m s * f s ^ 2 - (∑ s, m s * f s) ^ 2)) := by
  set μ := ∑ t, m t * f t with hμ
  have h1 : ∀ s, m s * Real.exp (lam * (f s - μ))
      ≤ m s * (lam ^ 2 * f s ^ 2 + (lam - 2 * lam ^ 2 * μ) * f s
          + (1 - lam * μ + lam ^ 2 * μ ^ 2) * (fun _ => (1 : ℝ)) s) := by
    intro s
    apply mul_le_mul_of_nonneg_left _ (hm0 s)
    have := Real.abs_exp_sub_one_sub_id_le (hb s)
    have h2 := (abs_le.mp this).2
    simp only
    nlinarith
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => h1 s)
  have e := bs1_lin m (fun s => f s ^ 2) f (fun _ => (1 : ℝ)) (lam ^ 2) (lam - 2 * lam ^ 2 * μ)
    (1 - lam * μ + lam ^ 2 * μ ^ 2)
  rw [e] at hsum
  have e1 : ∑ s, m s * (1 : ℝ) = 1 := by simpa using hm1
  rw [e1] at hsum
  have := Real.add_one_le_exp (lam ^ 2 * (∑ s, m s * f s ^ 2 - μ ^ 2))
  nlinarith

open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_chernoff {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (N : ℕ) (hN : 0 < N) (s0 : S) (a0 : A)
    (f : S → ℝ) (t lam : ℝ) (hlam : 0 ≤ lam)
    (hb : ∀ s, |lam * (f s - ∑ t, P s0 a0 t * f t)| ≤ 1) :
    sampleProb P N (fun x => t < ∑ s', empKernel x s0 a0 s' * f s' - ∑ s', P s0 a0 s' * f s')
      ≤ Real.exp (N * (lam ^ 2 * varP P f s0 a0 - lam * t)) := by
  set μ := ∑ s', P s0 a0 s' * f s' with hμ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ x : Samples S A N,
      (if t < ∑ s', empKernel x s0 a0 s' * f s' - μ then sampleWeight P x else 0)
        ≤ Real.exp (-(lam * N * t)) *
          (sampleWeight P x * ∏ i, Real.exp (lam * (f (x s0 a0 i) - μ))) := by
    intro x
    have hW := bs1_weight_nonneg P hP x
    split_ifs with hE
    · rw [bs1_emp_sum, lt_sub_iff_add_lt, lt_div_iff₀ hNr] at hE
      rw [← Real.exp_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h1 : 1 ≤ Real.exp (-(lam * N * t)) * Real.exp (lam * (∑ i, f (x s0 a0 i) - N * μ)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have : N * t ≤ ∑ i, f (x s0 a0 i) - N * μ := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this hlam]
      nlinarith
    · positivity
  have hmgf := bs1_mgf_one (P s0 a0) (hP s0 a0).1 (hP s0 a0).2 f lam hb
  unfold sampleProb
  calc (∑ x : Samples S A N,
        if t < ∑ s', empKernel x s0 a0 s' * f s' - μ then sampleWeight P x else 0)
      ≤ ∑ x : Samples S A N, Real.exp (-(lam * N * t)) *
          (sampleWeight P x * ∏ i, Real.exp (lam * (f (x s0 a0 i) - μ))) :=
        Finset.sum_le_sum (fun x _ => hterm x)
    _ = Real.exp (-(lam * N * t)) * (∑ s', P s0 a0 s' * Real.exp (lam * (f s' - μ))) ^ N := by
        rw [← Finset.mul_sum, bs1_mgf_prod P hP N s0 a0 (fun s' => Real.exp (lam * (f s' - μ)))]
    _ ≤ Real.exp (-(lam * N * t)) *
          (Real.exp (lam ^ 2 * (∑ s, P s0 a0 s * f s ^ 2 - μ ^ 2))) ^ N := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ _ hmgf
        exact Finset.sum_nonneg (fun s _ => mul_nonneg ((hP s0 a0).1 s) (Real.exp_pos _).le)
    _ = Real.exp (N * (lam ^ 2 * varP P f s0 a0 - lam * t)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simp only [varP]
        ring

-- one-sided Bernstein: upper tail
open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_bern_up {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (N : ℕ) (hN : 0 < N) (s0 : S) (a0 : A)
    (f : S → ℝ) (B L : ℝ) (hL : 0 ≤ L) (hf0 : ∀ s, 0 ≤ f s) (hfB : ∀ s, f s ≤ B) :
    sampleProb P N (fun x =>
      2 * Real.sqrt (L / N) * Real.sqrt (varP P f s0 a0) + 2 * L * B / N
        < ∑ s', empKernel x s0 a0 s' * f s' - ∑ s', P s0 a0 s' * f s') ≤ Real.exp (-L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set μ := ∑ s', P s0 a0 s' * f s' with hμ
  set σ2 := varP P f s0 a0 with hσ2
  have hσ2' : σ2 = ∑ s, P s0 a0 s * f s ^ 2 - μ ^ 2 := rfl
  have hσ0 : 0 ≤ σ2 := by
    have : (∑ s, P s0 a0 s * f s) ^ 2 ≤ ∑ s, P s0 a0 s * f s ^ 2 := by
      have h0 : 0 ≤ ∑ s, P s0 a0 s * (f s - μ) ^ 2 :=
        Finset.sum_nonneg (fun s _ => mul_nonneg ((hP s0 a0).1 s) (sq_nonneg _))
      have e := bs1_lin (P s0 a0) (fun s => f s ^ 2) f (fun _ => (1 : ℝ)) 1 (-2 * μ) (μ ^ 2)
      have e1 : ∑ s, P s0 a0 s * (1 : ℝ) = 1 := by simpa using (hP s0 a0).2
      rw [e1] at e
      have e2 : ∑ s, P s0 a0 s * (f s - μ) ^ 2
          = ∑ s, P s0 a0 s * (1 * f s ^ 2 + -2 * μ * f s + μ ^ 2 * 1) :=
        Finset.sum_congr rfl (fun s _ => by ring)
      rw [e2, e] at h0
      nlinarith
    rw [hσ2', hμ]; linarith
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg (fun s _ => mul_nonneg ((hP s0 a0).1 s) (hf0 s))
  have hμB : μ ≤ B := by
    calc μ ≤ ∑ s, P s0 a0 s * B :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hfB s) ((hP s0 a0).1 s))
      _ = B := by rw [← Finset.sum_mul, (hP s0 a0).2, one_mul]
  have hB0 : 0 ≤ B := le_trans (hf0 s0) (hfB s0)
  have hdev : ∀ s, |f s - μ| ≤ B := fun s => by
    rw [abs_le]; constructor <;> linarith [hf0 s, hfB s]
  set t := 2 * Real.sqrt (L / N) * Real.sqrt σ2 + 2 * L * B / N with ht
  have hsq1 : Real.sqrt (L / N) ^ 2 = L / N := Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt σ2 ^ 2 = σ2 := Real.sq_sqrt hσ0
  have ht0 : 0 ≤ t := by positivity
  rcases eq_or_lt_of_le hB0 with hB | hB
  · -- B = 0 : f = 0, event impossible
    have hf : ∀ s, f s = 0 := fun s => le_antisymm (hB ▸ hfB s) (hf0 s)
    have : sampleProb P N (fun x => t < ∑ s', empKernel x s0 a0 s' * f s' - μ) = 0 := by
      unfold sampleProb
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      simp only [hμ, hf, mul_zero, Finset.sum_const_zero, sub_zero, not_lt]
      exact ht0
    rw [this]; exact (Real.exp_pos _).le
  by_cases hcase : 2 * σ2 ≤ t * B
  · -- λ = 1/B
    have hb : ∀ s, |1 / B * (f s - μ)| ≤ 1 := fun s => by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / B), one_div, inv_mul_le_iff₀ hB, mul_one]
      exact hdev s
    refine le_trans (bs1_chernoff P hP N hN s0 a0 f t (1 / B) (by positivity) hb) ?_
    apply Real.exp_le_exp.mpr
    have h1 : (N : ℝ) * ((1 / B) ^ 2 * σ2 - 1 / B * t) ≤ -(N * t / (2 * B)) := by
      have : (1 / B) ^ 2 * σ2 ≤ t / (2 * B) := by
        rw [div_pow, one_pow, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e : 1 / B * t = t / B := by ring
      rw [e]
      have : (N : ℝ) * ((1 / B) ^ 2 * σ2 - t / B) ≤ N * (t / (2 * B) - t / B) :=
        mul_le_mul_of_nonneg_left (by linarith) hNr.le
      have e2 : (N : ℝ) * (t / (2 * B) - t / B) = -(N * t / (2 * B)) := by field_simp; ring
      linarith
    have h2 : L ≤ N * t / (2 * B) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * L * B / N * N = 2 * L * B := by field_simp
      have h3 : 0 ≤ 2 * Real.sqrt (L / N) * Real.sqrt σ2 := by positivity
      nlinarith
    linarith
  · -- λ = t/(2σ2)
    replace hcase := lt_of_not_ge hcase
    have hσpos : 0 < σ2 := by nlinarith
    have hlam0 : 0 ≤ t / (2 * σ2) := by positivity
    have hlamB : t / (2 * σ2) * B ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
    have hb : ∀ s, |t / (2 * σ2) * (f s - μ)| ≤ 1 := fun s => by
      rw [abs_mul, abs_of_nonneg hlam0]
      calc t / (2 * σ2) * |f s - μ| ≤ t / (2 * σ2) * B := mul_le_mul_of_nonneg_left (hdev s) hlam0
        _ ≤ 1 := hlamB
    refine le_trans (bs1_chernoff P hP N hN s0 a0 f t (t / (2 * σ2)) hlam0 hb) ?_
    apply Real.exp_le_exp.mpr
    have e : (N : ℝ) * ((t / (2 * σ2)) ^ 2 * σ2 - t / (2 * σ2) * t) = -(N * t ^ 2 / (4 * σ2)) := by
      field_simp; ring
    rw [e]
    have h4 : 4 * σ2 * L ≤ N * t ^ 2 := by
      have hA : 2 * Real.sqrt (L / N) * Real.sqrt σ2 ≤ t := by
        have : 0 ≤ 2 * L * B / N := by positivity
        linarith
      have hA2 : (2 * Real.sqrt (L / N) * Real.sqrt σ2) ^ 2 ≤ t ^ 2 :=
        pow_le_pow_left₀ (by positivity) hA 2
      have e3 : (2 * Real.sqrt (L / N) * Real.sqrt σ2) ^ 2 = 4 * (L / N) * σ2 := by
        rw [mul_pow, mul_pow, hsq1, hsq2]; ring
      rw [e3] at hA2
      have e4 : (N : ℝ) * (4 * (L / N) * σ2) = 4 * σ2 * L := by field_simp
      nlinarith
    have : L ≤ N * t ^ 2 / (4 * σ2) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith

-- ===== Part E: two-sided Bernstein, union bound, numerics, main =====

open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_sp_congr {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (N : ℕ) (E F : Samples S A N → Prop) (h : ∀ x, E x ↔ F x) :
    sampleProb P N E = sampleProb P N F := by
  have : E = F := funext (fun x => propext (h x))
  rw [this]

open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_union {S A ι : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (N : ℕ)
    (E : Samples S A N → Prop) (I : Finset ι) (F : ι → Samples S A N → Prop)
    (h : ∀ x, E x → ∃ i ∈ I, F i x) : sampleProb P N E ≤ ∑ i ∈ I, sampleProb P N (F i) := by
  unfold sampleProb
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hW := bs1_weight_nonneg P hP x
  split_ifs with hE
  · obtain ⟨i, hi, hF⟩ := h x hE
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun j _ => ?_) hi)
    · rw [if_pos hF]
    · split_ifs
      · exact hW
      · exact le_refl 0
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hW])

open BreakingSample.Perturbed FoundationsML.ReinforcementLearning in
theorem bs1_bern_two {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (N : ℕ) (hN : 0 < N) (s0 : S) (a0 : A)
    (f : S → ℝ) (B L : ℝ) (hL : 0 ≤ L) (hf0 : ∀ s, 0 ≤ f s) (hfB : ∀ s, f s ≤ B) :
    sampleProb P N (fun x =>
      2 * Real.sqrt (L / N) * Real.sqrt (varP P f s0 a0) + 2 * L * B / N
        < |∑ s', empKernel x s0 a0 s' * f s' - ∑ s', P s0 a0 s' * f s'|) ≤ 2 * Real.exp (-L) := by
  set g : S → ℝ := fun s => B - f s with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => by simp only [hg]; linarith [hfB s]
  have hgB : ∀ s, g s ≤ B := fun s => by simp only [hg]; linarith [hf0 s]
  have hP1 : ∑ s, P s0 a0 s * (1 : ℝ) = 1 := by simpa using (hP s0 a0).2
  have hvar : varP P g s0 a0 = varP P f s0 a0 := by
    simp only [varP]
    have e1 := bs1_lin (P s0 a0) (fun s => f s ^ 2) f (fun _ => (1 : ℝ)) 1 (-2 * B) (B ^ 2)
    have e2 := bs1_lin (P s0 a0) f f (fun _ => (1 : ℝ)) (-1) 0 B
    have e3 : ∑ s, P s0 a0 s * g s ^ 2
        = ∑ s, P s0 a0 s * (1 * f s ^ 2 + -2 * B * f s + B ^ 2 * 1) :=
      Finset.sum_congr rfl (fun s _ => by simp only [hg]; ring)
    have e4 : ∑ s, P s0 a0 s * g s = ∑ s, P s0 a0 s * (-1 * f s + 0 * f s + B * 1) :=
      Finset.sum_congr rfl (fun s _ => by simp only [hg]; ring)
    rw [e3, e4, e1, e2, hP1]
    ring
  have hdev : ∀ x : Samples S A N,
      (∑ s', empKernel x s0 a0 s' * g s' - ∑ s', P s0 a0 s' * g s')
        = -(∑ s', empKernel x s0 a0 s' * f s' - ∑ s', P s0 a0 s' * f s') := by
    intro x
    have hk := bs1_emp_kernel hN x
    have hE1 : ∑ s, empKernel x s0 a0 s * (1 : ℝ) = 1 := by simpa using (hk s0 a0).2
    have e1 := bs1_lin (empKernel x s0 a0) f f (fun _ => (1 : ℝ)) (-1) 0 B
    have e2 := bs1_lin (P s0 a0) f f (fun _ => (1 : ℝ)) (-1) 0 B
    have e3 : ∑ s, empKernel x s0 a0 s * g s
        = ∑ s, empKernel x s0 a0 s * (-1 * f s + 0 * f s + B * 1) :=
      Finset.sum_congr rfl (fun s _ => by simp only [hg]; ring)
    have e4 : ∑ s, P s0 a0 s * g s = ∑ s, P s0 a0 s * (-1 * f s + 0 * f s + B * 1) :=
      Finset.sum_congr rfl (fun s _ => by simp only [hg]; ring)
    rw [e3, e4, e1, e2, hE1, hP1]
    ring
  have hup := bs1_bern_up P hP N hN s0 a0 f B L hL hf0 hfB
  have hlo := bs1_bern_up P hP N hN s0 a0 g B L hL hg0 hgB
  rw [hvar] at hlo
  have hu := bs1_union P hP N (fun x => 2 * Real.sqrt (L / N) * Real.sqrt (varP P f s0 a0)
      + 2 * L * B / N < |∑ s', empKernel x s0 a0 s' * f s' - ∑ s', P s0 a0 s' * f s'|)
    (Finset.univ : Finset Bool)
    (fun (b : Bool) (x : Samples S A N) => 2 * Real.sqrt (L / N) * Real.sqrt (varP P f s0 a0) + 2 * L * B / N
        < (if b then 1 else -1) *
          (∑ s', empKernel x s0 a0 s' * f s' - ∑ s', P s0 a0 s' * f s'))
    (fun x hx => by
      rcases lt_abs.mp hx with h | h
      · exact ⟨true, Finset.mem_univ _, by simpa using h⟩
      · exact ⟨false, Finset.mem_univ _, by simpa using h⟩)
  refine le_trans hu ?_
  rw [Fintype.sum_bool]
  simp only [if_true, one_mul, Bool.false_eq_true, if_false, neg_one_mul]
  have hlo' : sampleProb P N (fun x => 2 * Real.sqrt (L / N) * Real.sqrt (varP P f s0 a0)
      + 2 * L * B / N < -(∑ s', empKernel x s0 a0 s' * f s' - ∑ s', P s0 a0 s' * f s'))
      ≤ Real.exp (-L) := by
    refine le_of_eq_of_le (bs1_sp_congr P N _ _ (fun x => ?_)) hlo
    rw [hdev x]
  linarith

theorem bs1_norm_sq_le {S : Type} [Fintype S] (f : S → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h0 : ∀ s, 0 ≤ f s) (h : ∀ s, f s ^ 2 ≤ K) : ‖f‖ ^ 2 ≤ K := by
  have hn : ‖f‖ ≤ Real.sqrt K := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 s)]
    exact Real.le_sqrt_of_sq_le (h s)
  have := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rwa [Real.sq_sqrt hK] at this

theorem bs1_num2 (E u ρ : ℝ) (hE : 2.7 < E) (hu0 : 0 ≤ u) (hu : 32 * E ^ 2 * u ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 = 8 * u) (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 2 * u) :
    ρ * (1 + b + 1 / 4) ≤ 1 / 4 := by
  have hE2 : 7.29 < E ^ 2 := by nlinarith
  have hu' : u * 233 ≤ 1 := by nlinarith
  have h2 : (2 * E * ρ) ^ 2 ≤ 1 := by nlinarith
  have h3 : 2 * E * ρ ≤ 1 := by
    have h0 : 0 ≤ 2 * E * ρ := by positivity
    nlinarith
  have h4 : ρ ≤ 1 / 5.4 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  nlinarith

theorem bs1_num3 (E u γ ρ θ : ℝ) (m : ℕ) (hm : 1 ≤ m) (hE : 2.7 < E) (hu0 : 0 ≤ u)
    (hu : 32 * E ^ 2 * u ≤ 1) (hγ1 : 0 < 1 - γ) (hEm : 1 / (1 - γ) ≤ E ^ m)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 = 8 * u) (hθ0 : 0 ≤ θ) (hθ : θ ^ 2 ≤ 4 * u / (1 - γ)) :
    ρ ^ (m - 1) * θ ≤ 1 / 4 := by
  have hm' : m = (m - 1) + 1 := by omega
  have h8 : 8 * u * E ≤ 1 / 10 := by nlinarith
  have hpow : (8 * u * E) ^ m ≤ 8 * u * E :=
    pow_le_of_le_one (by positivity) (by linarith) (by omega)
  have hsq : (ρ ^ (m - 1) * θ) ^ 2 ≤ 1 / 16 := by
    have e1 : (ρ ^ (m - 1)) ^ 2 = (8 * u) ^ (m - 1) := by rw [← pow_mul, mul_comm, pow_mul, hρ]
    have h1 : (ρ ^ (m - 1) * θ) ^ 2 ≤ (8 * u) ^ (m - 1) * (4 * u / (1 - γ)) := by
      rw [mul_pow, e1]
      exact mul_le_mul_of_nonneg_left hθ (by positivity)
    have h2 : (8 * u) ^ (m - 1) * (4 * u / (1 - γ)) = (8 * u) ^ m / 2 * (1 / (1 - γ)) := by
      conv_rhs => rw [hm', pow_succ]
      field_simp
      ring
    have h3 : (8 * u) ^ m / 2 * (1 / (1 - γ)) ≤ (8 * u) ^ m / 2 * E ^ m :=
      mul_le_mul_of_nonneg_left hEm (by positivity)
    have h4 : (8 * u) ^ m / 2 * E ^ m = (8 * u * E) ^ m / 2 := by rw [mul_pow]; ring
    have h5 : 8 * u * E / 2 ≤ 1 / 16 := by linarith
    linarith
  have h0 : 0 ≤ ρ ^ (m - 1) * θ := by positivity
  nlinarith

theorem bs1_numerics (γ L Nr E : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hL : 0 < L) (hNr : 0 < Nr)
    (hE27 : 2.7 < E) (hN : 32 * E ^ 2 / (1 - γ) * L ≤ Nr) (m : ℕ) (hm1 : 1 ≤ m)
    (hEm : 1 / (1 - γ) ≤ E ^ m) :
    Real.sqrt (2 * (2 * Real.sqrt (L / Nr)) ^ 2 / (1 - γ))
        * (1 + γ * (2 * L / Nr) / (1 - γ) + 1 / 4) ≤ 1 / 4 ∧
      Real.sqrt (2 * (2 * Real.sqrt (L / Nr)) ^ 2 / (1 - γ)) ^ (m - 1)
        * (γ * (2 * Real.sqrt (L / Nr)) / (1 - γ)) ≤ 1 / 4 ∧
      γ * (2 * L / Nr) / (1 - γ) ≤ 1 / 10 ∧ L / (Nr * (1 - γ)) * 200 ≤ 1 := by
  have h1γ : 0 < 1 - γ := by linarith
  set α := 2 * Real.sqrt (L / Nr) with hαdef
  set β := 2 * L / Nr with hβdef
  set u := L / (Nr * (1 - γ)) with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu : 32 * E ^ 2 * u ≤ 1 := by
    rw [hudef, mul_div_assoc', div_le_one (by positivity)]
    have : 32 * E ^ 2 / (1 - γ) * L * (1 - γ) = 32 * E ^ 2 * L := by field_simp
    nlinarith
  have hu' : u * 200 ≤ 1 := by nlinarith
  set ρ := Real.sqrt (2 * α ^ 2 / (1 - γ)) with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hα2 : α ^ 2 = 4 * (L / Nr) := by
    rw [hαdef, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hρ2 : ρ ^ 2 = 2 * α ^ 2 / (1 - γ) := Real.sq_sqrt (by positivity)
  have hρ8 : ρ ^ 2 = 8 * u := by
    rw [hρ2, hα2, hudef]; first | (field_simp; ring) | field_simp
  have hb2 : γ * β / (1 - γ) ≤ 2 * u := by
    rw [hβdef, hudef, div_le_iff₀ h1γ]
    have : 2 * (L / (Nr * (1 - γ))) * (1 - γ) = 2 * L / Nr := by field_simp
    rw [this]
    have : γ * (2 * L / Nr) ≤ 1 * (2 * L / Nr) := mul_le_mul_of_nonneg_right hγ1.le (by positivity)
    linarith
  have hb20 : 0 ≤ γ * β / (1 - γ) := by positivity
  have hθ : (γ * α / (1 - γ)) ^ 2 ≤ 4 * u / (1 - γ) := by
    have e : 4 * u / (1 - γ) = α ^ 2 / (1 - γ) ^ 2 := by
      rw [hα2, hudef]; first | (field_simp; ring) | field_simp
    rw [e, div_pow, mul_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg α]
  refine ⟨bs1_num2 E u ρ hE27 hu0 hu hρ0 hρ8 _ hb20 hb2,
    bs1_num3 E u γ ρ (γ * α / (1 - γ)) m hm1 hE27 hu0 hu h1γ hEm hρ0 hρ8 (by positivity) hθ,
    by linarith, hu'⟩

theorem bs1_second (γ L Nr x0 x1 : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hL : 0 < L) (hNr : 0 < Nr)
    (hx0n : 0 ≤ x0) (hx1n : 0 ≤ x1) (hx0 : x0 ≤ 1 / (1 - γ))
    (hx1 : x1 ^ 2 ≤ 2 * x0 ^ 2 / (γ ^ 2 * (1 - γ))) (hu' : L / (Nr * (1 - γ)) * 200 ≤ 1) :
    4 * γ * Real.sqrt (2 * L / Nr) * x1 + 2 * γ * L / ((1 - γ) * Nr) * x0
      ≤ 6 * Real.sqrt (2 * L / (Nr * (1 - γ) ^ 3)) := by
  have h1γ : 0 < 1 - γ := by linarith
  set X := Real.sqrt (2 * L / (Nr * (1 - γ) ^ 3)) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = 2 * L / (Nr * (1 - γ) ^ 3) := Real.sq_sqrt (by positivity)
  have hs2' : Real.sqrt 2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hgx : (γ * x1) ^ 2 ≤ 2 / (1 - γ) ^ 3 := by
    have h1 : (γ * x1) ^ 2 ≤ 2 * x0 ^ 2 / (1 - γ) := by
      rw [mul_pow]
      have := mul_le_mul_of_nonneg_left hx1 (sq_nonneg γ)
      have e : γ ^ 2 * (2 * x0 ^ 2 / (γ ^ 2 * (1 - γ))) = 2 * x0 ^ 2 / (1 - γ) := by
        field_simp
      linarith
    have h2 : x0 ^ 2 ≤ (1 / (1 - γ)) ^ 2 := pow_le_pow_left₀ hx0n hx0 2
    have h3 : 2 * x0 ^ 2 / (1 - γ) ≤ 2 * (1 / (1 - γ)) ^ 2 / (1 - γ) :=
      div_le_div_of_nonneg_right (by linarith) h1γ.le
    have e : 2 * (1 / (1 - γ)) ^ 2 / (1 - γ) = 2 / (1 - γ) ^ 3 := by
      first | (field_simp; ring) | field_simp
    linarith
  have hA : (Real.sqrt (2 * L / Nr) * (γ * x1)) ^ 2 ≤ (Real.sqrt 2 * X) ^ 2 := by
    rw [mul_pow (Real.sqrt (2 * L / Nr)) (γ * x1) 2, mul_pow (Real.sqrt 2) X 2,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num), hX2]
    have e : 2 * (2 * L / (Nr * (1 - γ) ^ 3)) = 2 * L / Nr * (2 / (1 - γ) ^ 3) := by
      first | (field_simp; ring) | field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hgx (by positivity)
  have hA' : Real.sqrt (2 * L / Nr) * (γ * x1) ≤ Real.sqrt 2 * X :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hA
  have hY : (X * (1 - γ)) ^ 2 ≤ 1 / 100 := by
    rw [mul_pow, hX2]
    have e : 2 * L / (Nr * (1 - γ) ^ 3) * (1 - γ) ^ 2 = 2 * (L / (Nr * (1 - γ))) := by
      first | (field_simp; ring) | field_simp
    rw [e]
    nlinarith
  have hY' : X * (1 - γ) ≤ 1 / 10 := by
    have h0 : 0 ≤ X * (1 - γ) := by positivity
    nlinarith
  have hB : 2 * γ * L / ((1 - γ) * Nr) * x0 ≤ X * (X * (1 - γ)) := by
    have h1 : 2 * γ * L / ((1 - γ) * Nr) * x0 ≤ 2 * L / ((1 - γ) * Nr) * (1 / (1 - γ)) := by
      apply mul_le_mul _ hx0 hx0n (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have e : 2 * L / ((1 - γ) * Nr) * (1 / (1 - γ)) = X * (X * (1 - γ)) := by
      rw [show X * (X * (1 - γ)) = X ^ 2 * (1 - γ) by ring, hX2]
      first | (field_simp; ring) | field_simp
    linarith
  have hB' : X * (X * (1 - γ)) ≤ X * (1 / 10) := mul_le_mul_of_nonneg_left hY' hX0
  have e4 : 4 * γ * Real.sqrt (2 * L / Nr) * x1 = 4 * (Real.sqrt (2 * L / Nr) * (γ * x1)) := by ring
  rw [e4]
  nlinarith

theorem bs1_final {S : Type} [Fintype S] [DecidableEq S] (M Mh : Matrix S S ℝ)
    (hM0 : ∀ s s', 0 ≤ M s s') (hM1 : ∀ s, ∑ s', M s s' = 1)
    (hMh0 : ∀ s s', 0 ≤ Mh s s') (hMh1 : ∀ s, ∑ s', Mh s s' = 1)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (V w : ℕ → S → ℝ) (Vh : S → ℝ)
    (hV : ∀ l s, V l s = w l s + γ * ∑ s', M s s' * V l s')
    (hw0 : ∀ s, 0 ≤ w 0 s) (hw0' : ∀ s, w 0 s ≤ 1)
    (hwS : ∀ l s, w (l + 1) s = Real.sqrt (∑ s', M s s' * V l s' ^ 2 - (∑ s', M s s' * V l s') ^ 2))
    (hVh : ∀ s, Vh s = w 0 s + γ * ∑ s', Mh s s' * Vh s')
    (L Nr E : ℝ) (hL : 0 < L) (hNr : 0 < Nr) (hE27 : 2.7 < E)
    (hN : 32 * E ^ 2 / (1 - γ) * L ≤ Nr) (m : ℕ) (hm1 : 1 ≤ m) (hEm : 1 / (1 - γ) ≤ E ^ m)
    (hE : ∀ l, l ≤ m → ∀ s, |∑ s', Mh s s' * V l s' - ∑ s', M s s' * V l s'|
        ≤ 2 * Real.sqrt (L / Nr) * w (l + 1) s + 2 * L * ‖V l‖ / Nr) :
    ‖fun s => Vh s - V 0 s‖
        ≤ 4 * γ * Real.sqrt (2 * L / Nr) * ‖V 1‖ + 2 * γ * L / ((1 - γ) * Nr) * ‖V 0‖ ∧
      4 * γ * Real.sqrt (2 * L / Nr) * ‖V 1‖ + 2 * γ * L / ((1 - γ) * Nr) * ‖V 0‖
        ≤ 6 * Real.sqrt (2 * L / (Nr * (1 - γ) ^ 3)) := by
  have h1γ : 0 < 1 - γ := by linarith
  obtain ⟨hn2, hn3, hb, hu'⟩ := bs1_numerics γ L Nr E hγ0 hγ1 hL hNr hE27 hN m hm1 hEm
  have hwnn : ∀ l s, 0 ≤ w l s := by
    intro l s; cases l with
    | zero => exact hw0 s
    | succ l => rw [hwS]; exact Real.sqrt_nonneg _
  have hVnn : ∀ l s, 0 ≤ V l s := fun l =>
    bs1_nonneg M hM0 hM1 γ hγ0.le hγ1 (w l) (V l) (hwnn l) (hV l)
  have hx0n : 0 ≤ ‖V 0‖ := norm_nonneg _
  have hx1n : 0 ≤ ‖V 1‖ := norm_nonneg _
  have hx0 : ‖V 0‖ ≤ 1 / (1 - γ) := by
    have hup := bs1_upper M hM0 hM1 γ hγ0.le hγ1 (w 0) (V 0) 1 hw0' (hV 0)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (hVnn 0 s)]
    exact hup s
  have hx1 : ‖V 1‖ ^ 2 ≤ 2 * ‖V 0‖ ^ 2 / (γ ^ 2 * (1 - γ)) := by
    have hv := bs1_var M hM0 hM1 γ hγ0 hγ1 (w 0) (V 0) (V 1) ‖V 0‖ hw0 (hV 0) (hVnn 0)
      (fun s => bs1_norm_le (V 0) s) (fun s => by rw [hV 1 s, hwS 0 s])
    exact bs1_norm_sq_le (V 1) _ (by positivity) (hVnn 1) hv
  refine ⟨?_, bs1_second γ L Nr ‖V 0‖ ‖V 1‖ hγ0 hγ1 hL hNr hx0n hx1n hx0 hx1 hu'⟩
  have hE' : ∀ l, l ≤ m → ∀ s, |∑ s', Mh s s' * V l s' - ∑ s', M s s' * V l s'|
      ≤ 2 * Real.sqrt (L / Nr) * w (l + 1) s + 2 * L / Nr * ‖V l‖ := by
    intro l hl s
    have := hE l hl s
    rw [show 2 * L / Nr * ‖V l‖ = 2 * L * ‖V l‖ / Nr by ring]
    exact this
  have hd := bs1_det M Mh hM0 hM1 hMh0 hMh1 γ hγ0 hγ1 V w Vh hV hw0 hwS hVh
    (2 * Real.sqrt (L / Nr)) (2 * L / Nr) _ (by positivity) (by positivity) (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by positivity)) m hm1 hn2 hn3 hE'
  have hsq2 : Real.sqrt (2 * L / Nr) = Real.sqrt 2 * Real.sqrt (L / Nr) := by
    rw [← Real.sqrt_mul (by norm_num)]; ring_nf
  have hs2 : 1.4 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hsL : 0 ≤ Real.sqrt (L / Nr) := Real.sqrt_nonneg _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro s
  rw [Real.norm_eq_abs]
  refine le_trans (hd s) ?_
  have t1 : γ * (2 * Real.sqrt (L / Nr)) * (3 / 2 + γ * (2 * L / Nr) / (1 - γ)) * ‖V 1‖
      ≤ 4 * γ * Real.sqrt (2 * L / Nr) * ‖V 1‖ := by
    rw [hsq2]
    have h0 : 0 ≤ γ * Real.sqrt (L / Nr) * ‖V 1‖ := by positivity
    nlinarith
  have t2 : γ * (2 * L / Nr) * ‖V 0‖ / (1 - γ) = 2 * γ * L / ((1 - γ) * Nr) * ‖V 0‖ := by
    first | (field_simp; ring) | field_simp
  linarith

open Matrix in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (π : S → A) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (N : ℕ) :
    let L : ℝ := Real.log (4 * (Fintype.card S : ℝ) * Real.log (Real.exp 1 / (1 - γ)) / δ)
    32 * Real.exp 1 ^ 2 / (1 - γ) * L ≤ (N : ℝ) →
    BreakingSample.Perturbed.sampleProb P N (fun x =>
      ¬ (‖fun s => BreakingSample.Perturbed.value (BreakingSample.Perturbed.empKernel x) r γ π s - BreakingSample.Perturbed.value P r γ π s‖
            ≤ 4 * γ * Real.sqrt (2 * L / N)
                * ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.value P r γ π) s))‖
              + 2 * γ * L / ((1 - γ) * N) * ‖BreakingSample.Perturbed.value P r γ π‖ ∧
         4 * γ * Real.sqrt (2 * L / N)
                * ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.value P r γ π) s))‖
              + 2 * γ * L / ((1 - γ) * N) * ‖BreakingSample.Perturbed.value P r γ π‖
            ≤ 6 * Real.sqrt (2 * L / (N * (1 - γ) ^ 3)))) ≤ δ := by
  intro L hN
  obtain ⟨hP, hr, hγ0, hγ1, hS, -⟩ := hM
  have h1γ : 0 < 1 - γ := by linarith
  set E := Real.exp 1 with hEdef
  have hE27 : 2.7 < E := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hEpos : 0 < E := Real.exp_pos 1
  set K := Real.log (E / (1 - γ)) with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef, Real.log_div hEpos.ne' h1γ.ne', hEdef, Real.log_exp]
    have : Real.log (1 - γ) ≤ 0 := Real.log_nonpos h1γ.le (by linarith)
    linarith
  have hcard : (1 : ℝ) ≤ Fintype.card S := by
    have := Fintype.card_pos (α := S)
    exact_mod_cast this
  have harg : 0 < 4 * (Fintype.card S : ℝ) * K / δ := by positivity
  have hLpos : 0 < L := by
    show 0 < Real.log (4 * (Fintype.card S : ℝ) * K / δ)
    apply Real.log_pos
    rw [lt_div_iff₀ hδ₀]; nlinarith
  have hexpL : Real.exp (-L) = δ / (4 * Fintype.card S * K) := by
    rw [Real.exp_neg]
    show (Real.exp (Real.log (4 * (Fintype.card S : ℝ) * K / δ)))⁻¹ = _
    rw [Real.exp_log harg, inv_div]
  have hNr : 0 < (N : ℝ) := lt_of_lt_of_le (mul_pos (div_pos (by positivity) h1γ) hLpos) hN
  have hNpos : 0 < N := by exact_mod_cast hNr
  set m := ⌊K⌋₊ with hmdef
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hK1)
  have hmK : (m : ℝ) ≤ K := Nat.floor_le (by linarith)
  have hKm : K < m + 1 := Nat.lt_floor_add_one K
  have hEm : 1 / (1 - γ) ≤ E ^ m := by
    have h0 : Real.log (E / (1 - γ)) < (m : ℝ) + 1 := hKm
    have h1 : E / (1 - γ) < Real.exp ((m : ℝ) + 1) :=
      (Real.log_lt_iff_lt_exp (div_pos hEpos h1γ)).mp h0
    have h2 : Real.exp ((m : ℝ) + 1) = E ^ m * E := by
      rw [Real.exp_add, hEdef, ← Real.exp_nat_mul, mul_one]
    rw [h2] at h1
    have h3 : E / (1 - γ) = (1 / (1 - γ)) * E := by ring
    rw [h3] at h1
    exact (lt_of_mul_lt_mul_right h1 hEpos.le).le
  -- the vectors
  set V : ℕ → S → ℝ := fun l => BreakingSample.Perturbed.auxV P r γ π l with hVdef
  set w : ℕ → S → ℝ := fun l => Nat.casesOn l (BreakingSample.Perturbed.policyReward r π)
    (fun l => fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (V l) s)) with hwdef
  set M := BreakingSample.Perturbed.policyMatrix P π with hMdef
  have hM0 : ∀ s s', 0 ≤ M s s' := fun s s' => (hP s (π s)).1 s'
  have hM1 : ∀ s, ∑ s', M s s' = 1 := fun s => (hP s (π s)).2
  have hV0 : V 0 = fun s => BreakingSample.Perturbed.value P r γ π s :=
    bs1_aux_zero P hP r γ hγ0.le hγ1 π
  have hV : ∀ l s, V l s = w l s + γ * ∑ s', M s s' * V l s' := by
    intro l s
    cases l with
    | zero =>
      rw [hV0]
      exact bs1_value_bellman P hP r γ hγ0.le hγ1 π s
    | succ l => exact bs1_aux_fix P hP r γ hγ0.le hγ1 π l s
  have hw0 : ∀ s, 0 ≤ w 0 s := fun s => (hr s (π s)).1
  have hw0' : ∀ s, w 0 s ≤ 1 := fun s => (hr s (π s)).2
  have hwS : ∀ l s, w (l + 1) s
      = Real.sqrt (∑ s', M s s' * V l s' ^ 2 - (∑ s', M s s' * V l s') ^ 2) := fun l s => rfl
  have hwnn : ∀ l s, 0 ≤ w l s := by
    intro l s; cases l with
    | zero => exact hw0 s
    | succ l => rw [hwS]; exact Real.sqrt_nonneg _
  have hVnn : ∀ l s, 0 ≤ V l s := fun l =>
    bs1_nonneg M hM0 hM1 γ hγ0.le hγ1 (w l) (V l) (hwnn l) (hV l)
  have hV1eq : BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt
      (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.value P r γ π) s)) = V 1 := by
    show _ = BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt
      (BreakingSample.Perturbed.varPi P π (V 0) s))
    rw [hV0]
  have hV0eq : BreakingSample.Perturbed.value P r γ π = V 0 := by rw [hV0]
  rw [hV1eq, hV0eq]
  -- the deterministic implication on the good event
  have hdet : ∀ x : BreakingSample.Perturbed.Samples S A N,
      (∀ l, l ≤ m → ∀ s, ¬ (2 * Real.sqrt (L / N) *
          Real.sqrt (BreakingSample.Perturbed.varP P (V l) s (π s)) + 2 * L * ‖V l‖ / N
        < |∑ s', BreakingSample.Perturbed.empKernel x s (π s) s' * V l s'
            - ∑ s', P s (π s) s' * V l s'|)) →
      (‖fun s => BreakingSample.Perturbed.value (BreakingSample.Perturbed.empKernel x) r γ π s - V 0 s‖
            ≤ 4 * γ * Real.sqrt (2 * L / N) * ‖V 1‖ + 2 * γ * L / ((1 - γ) * N) * ‖V 0‖ ∧
         4 * γ * Real.sqrt (2 * L / N) * ‖V 1‖ + 2 * γ * L / ((1 - γ) * N) * ‖V 0‖
            ≤ 6 * Real.sqrt (2 * L / (N * (1 - γ) ^ 3))) := by
    intro x hx
    have hk := bs1_emp_kernel hNpos x
    exact bs1_final M (BreakingSample.Perturbed.policyMatrix (BreakingSample.Perturbed.empKernel x) π)
      hM0 hM1 (fun s s' => (hk s (π s)).1 s') (fun s => (hk s (π s)).2) γ hγ0 hγ1 V w
      (fun s => BreakingSample.Perturbed.value (BreakingSample.Perturbed.empKernel x) r γ π s)
      hV hw0 hw0' hwS
      (bs1_value_bellman (BreakingSample.Perturbed.empKernel x) hk r γ hγ0.le hγ1 π)
      L N E hLpos hNr hE27 hN m hm1 hEm (fun l hl s => not_lt.mp (hx l hl s))
  -- union bound
  have hcover : ∀ x : BreakingSample.Perturbed.Samples S A N,
      ¬ (‖fun s => BreakingSample.Perturbed.value (BreakingSample.Perturbed.empKernel x) r γ π s - V 0 s‖
            ≤ 4 * γ * Real.sqrt (2 * L / N) * ‖V 1‖ + 2 * γ * L / ((1 - γ) * N) * ‖V 0‖ ∧
         4 * γ * Real.sqrt (2 * L / N) * ‖V 1‖ + 2 * γ * L / ((1 - γ) * N) * ‖V 0‖
            ≤ 6 * Real.sqrt (2 * L / (N * (1 - γ) ^ 3))) →
      ∃ i ∈ (Finset.range (m + 1) ×ˢ (Finset.univ : Finset S)),
        (fun (i : ℕ × S) (x : BreakingSample.Perturbed.Samples S A N) => 2 * Real.sqrt (L / N) *
          Real.sqrt (BreakingSample.Perturbed.varP P (V i.1) i.2 (π i.2))
          + 2 * L * ‖V i.1‖ / N
          < |∑ s', BreakingSample.Perturbed.empKernel x i.2 (π i.2) s' * V i.1 s'
              - ∑ s', P i.2 (π i.2) s' * V i.1 s'|) i x := by
    intro x hbad
    by_contra hno
    refine hbad (hdet x (fun l hl s hlt => hno ⟨(l, s), ?_, hlt⟩))
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_univ s⟩
  refine le_trans (bs1_union P hP N _ _ _ hcover) ?_
  have hterm : ∀ i ∈ (Finset.range (m + 1) ×ˢ (Finset.univ : Finset S)),
      BreakingSample.Perturbed.sampleProb P N (fun x => 2 * Real.sqrt (L / N) *
          Real.sqrt (BreakingSample.Perturbed.varP P (V i.1) i.2 (π i.2))
          + 2 * L * ‖V i.1‖ / N
          < |∑ s', BreakingSample.Perturbed.empKernel x i.2 (π i.2) s' * V i.1 s'
              - ∑ s', P i.2 (π i.2) s' * V i.1 s'|) ≤ 2 * Real.exp (-L) := by
    intro i _
    exact bs1_bern_two P hP N hNpos i.2 (π i.2) (V i.1) ‖V i.1‖ L hLpos.le (hVnn i.1)
      (fun s => bs1_norm_le (V i.1) s)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hfin : ((m : ℝ) + 1) * (Fintype.card S : ℝ) * (2 * (δ / (4 * Fintype.card S * K))) ≤ δ := by
    have hmK2 : (m : ℝ) + 1 ≤ 2 * K := by linarith
    have e : ((m : ℝ) + 1) * (Fintype.card S : ℝ) * (2 * (δ / (4 * Fintype.card S * K)))
        = ((m : ℝ) + 1) * δ / (2 * K) := by
      first | (field_simp; ring) | field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_univ, nsmul_eq_mul,
    hexpL]
  refine le_trans (le_of_eq ?_) hfin
  push_cast
  ring
