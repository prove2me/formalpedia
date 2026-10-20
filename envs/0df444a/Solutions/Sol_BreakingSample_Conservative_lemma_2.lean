-- Prove2me | solution 1 for BreakingSample.Conservative.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T03:39:25.471806+00:00
-- url     : https://prove2.me/submissions/310eefea-68e9-49fc-a777-4b9f6c016f61

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model

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

-- ===== lemma_2 numerics =====

theorem bs1_norm_sq_le {S : Type} [Fintype S] (f : S → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h0 : ∀ s, 0 ≤ f s) (h : ∀ s, f s ^ 2 ≤ K) : ‖f‖ ^ 2 ≤ K := by
  have hn : ‖f‖ ≤ Real.sqrt K := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 s)]
    exact Real.le_sqrt_of_sq_le (h s)
  have := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rwa [Real.sq_sqrt hK] at this


theorem bs2_num2 (E u ρ : ℝ) (hE : 2.7 < E) (hu0 : 0 ≤ u) (hu : 16 * E ^ 2 * u ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 = 2 * u) (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ u) :
    ρ * (1 + b + 1 / 4) ≤ 1 / 4 := by
  have hE2 : 7.29 < E ^ 2 := by nlinarith
  have hu' : u * 116 ≤ 1 := by nlinarith
  have h4 : ρ ≤ 1 / 7 := by nlinarith
  have hb' : b ≤ 1 / 100 := by linarith
  have h5 : ρ * (1 + b + 1 / 4) ≤ (1 / 7) * (1 + 1 / 100 + 1 / 4) :=
    mul_le_mul h4 (by linarith) (by positivity) (by norm_num)
  linarith

theorem bs2_num3 (E u γ ρ θ : ℝ) (m : ℕ) (hm : 1 ≤ m) (hE : 2.7 < E) (hu0 : 0 ≤ u)
    (hu : 16 * E ^ 2 * u ≤ 1) (hγ1 : 0 < 1 - γ) (hEm : 1 / (1 - γ) ≤ E ^ m)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ^ 2 = 2 * u) (hθ0 : 0 ≤ θ) (hθ : θ ^ 2 ≤ u / (1 - γ)) :
    ρ ^ (m - 1) * θ ≤ 1 / 4 := by
  have hm' : m = (m - 1) + 1 := by omega
  have h8 : 2 * u * E ≤ 1 / 10 := by nlinarith
  have hpow : (2 * u * E) ^ m ≤ 2 * u * E :=
    pow_le_of_le_one (by positivity) (by linarith) (by omega)
  have hsq : (ρ ^ (m - 1) * θ) ^ 2 ≤ 1 / 16 := by
    have e1 : (ρ ^ (m - 1)) ^ 2 = (2 * u) ^ (m - 1) := by rw [← pow_mul, mul_comm, pow_mul, hρ]
    have h1 : (ρ ^ (m - 1) * θ) ^ 2 ≤ (2 * u) ^ (m - 1) * (u / (1 - γ)) := by
      rw [mul_pow, e1]
      exact mul_le_mul_of_nonneg_left hθ (by positivity)
    have h2 : (2 * u) ^ (m - 1) * (u / (1 - γ)) = (2 * u) ^ m / 2 * (1 / (1 - γ)) := by
      conv_rhs => rw [hm', pow_succ]
      first | (field_simp; ring) | field_simp
    have h3 : (2 * u) ^ m / 2 * (1 / (1 - γ)) ≤ (2 * u) ^ m / 2 * E ^ m :=
      mul_le_mul_of_nonneg_left hEm (by positivity)
    have h4 : (2 * u) ^ m / 2 * E ^ m = (2 * u * E) ^ m / 2 := by rw [mul_pow]; ring
    have h5 : 2 * u * E / 2 ≤ 1 / 16 := by linarith
    linarith
  have h0 : 0 ≤ ρ ^ (m - 1) * θ := by positivity
  nlinarith

theorem bs2_numerics (γ b Nr E : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : 0 < b) (hNr : 0 < Nr)
    (hE27 : 2.7 < E) (hN : 16 * E ^ 2 / (1 - γ) * b < Nr) (m : ℕ) (hm1 : 1 ≤ m)
    (hEm : 1 / (1 - γ) ≤ E ^ m) :
    Real.sqrt (2 * Real.sqrt (b / Nr) ^ 2 / (1 - γ))
        * (1 + γ * (b / Nr) / (1 - γ) + 1 / 4) ≤ 1 / 4 ∧
      Real.sqrt (2 * Real.sqrt (b / Nr) ^ 2 / (1 - γ)) ^ (m - 1)
        * (γ * Real.sqrt (b / Nr) / (1 - γ)) ≤ 1 / 4 ∧
      b / (Nr * (1 - γ)) * 100 ≤ 1 := by
  have h1γ : 0 < 1 - γ := by linarith
  set α := Real.sqrt (b / Nr) with hαdef
  set u := b / (Nr * (1 - γ)) with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu : 16 * E ^ 2 * u ≤ 1 := by
    rw [hudef, mul_div_assoc', div_le_one (by positivity)]
    have : 16 * E ^ 2 / (1 - γ) * b * (1 - γ) = 16 * E ^ 2 * b := by field_simp
    nlinarith
  have hu' : u * 100 ≤ 1 := by nlinarith
  set ρ := Real.sqrt (2 * α ^ 2 / (1 - γ)) with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hα2 : α ^ 2 = b / Nr := by
    rw [hαdef, Real.sq_sqrt (by positivity)]
  have hρ2 : ρ ^ 2 = 2 * α ^ 2 / (1 - γ) := Real.sq_sqrt (by positivity)
  have hρ8 : ρ ^ 2 = 2 * u := by
    rw [hρ2, hα2, hudef]; first | (field_simp; ring) | field_simp
  have hb2 : γ * (b / Nr) / (1 - γ) ≤ u := by
    rw [hudef, div_le_iff₀ h1γ]
    have : b / (Nr * (1 - γ)) * (1 - γ) = b / Nr := by field_simp
    rw [this]
    have : γ * (b / Nr) ≤ 1 * (b / Nr) := mul_le_mul_of_nonneg_right hγ1.le (by positivity)
    linarith
  have hb20 : 0 ≤ γ * (b / Nr) / (1 - γ) := by positivity
  have hθ : (γ * α / (1 - γ)) ^ 2 ≤ u / (1 - γ) := by
    have e : u / (1 - γ) = α ^ 2 / (1 - γ) ^ 2 := by
      rw [hα2, hudef]; first | (field_simp; ring) | field_simp
    rw [e, div_pow, mul_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg α]
  exact ⟨bs2_num2 E u ρ hE27 hu0 hu hρ0 hρ8 _ hb20 hb2,
    bs2_num3 E u γ ρ (γ * α / (1 - γ)) m hm1 hE27 hu0 hu h1γ hEm hρ0 hρ8 (by positivity) hθ,
    hu'⟩

theorem bs2_second (γ b Nr x0 x1 : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hb : 0 < b) (hNr : 0 < Nr)
    (hx0n : 0 ≤ x0) (hx1n : 0 ≤ x1) (hx0 : x0 ≤ 1 / (1 - γ))
    (hx1 : x1 ^ 2 ≤ 2 * x0 ^ 2 / (γ ^ 2 * (1 - γ))) (hu : b / (Nr * (1 - γ)) * 100 ≤ 1) :
    γ * Real.sqrt (b / Nr) * (3 / 2 + γ * (b / Nr) / (1 - γ)) * x1 + γ * (b / Nr) * x0 / (1 - γ)
      ≤ 6 / (1 - γ) * Real.sqrt (b / (Nr * (1 - γ))) := by
  have h1γ : 0 < 1 - γ := by linarith
  set X := Real.sqrt (b / (Nr * (1 - γ))) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = b / (Nr * (1 - γ)) := Real.sq_sqrt (by positivity)
  have hX1 : X ≤ 1 / 10 := by nlinarith
  set Q := X / (1 - γ) with hQdef
  have hQ0 : 0 ≤ Q := by positivity
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
  have hA : (Real.sqrt (b / Nr) * (γ * x1)) ^ 2 ≤ (Real.sqrt 2 * Q) ^ 2 := by
    rw [mul_pow (Real.sqrt (b / Nr)) (γ * x1) 2, mul_pow (Real.sqrt 2) Q 2,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num), hQdef, div_pow, hX2]
    have e : 2 * (b / (Nr * (1 - γ)) / (1 - γ) ^ 2) = b / Nr * (2 / (1 - γ) ^ 3) := by
      first | (field_simp; ring) | field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hgx (by positivity)
  have hA' : Real.sqrt (b / Nr) * (γ * x1) ≤ Real.sqrt 2 * Q :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hA
  have hc : γ * (b / Nr) / (1 - γ) ≤ 1 / 100 := by
    have : γ * (b / Nr) / (1 - γ) ≤ b / (Nr * (1 - γ)) := by
      rw [div_le_iff₀ h1γ]
      have : b / (Nr * (1 - γ)) * (1 - γ) = b / Nr := by field_simp
      rw [this]
      have : γ * (b / Nr) ≤ 1 * (b / Nr) := mul_le_mul_of_nonneg_right hγ1.le (by positivity)
      linarith
    linarith
  have hc0 : 0 ≤ γ * (b / Nr) / (1 - γ) := by positivity
  have hB : γ * (b / Nr) * x0 / (1 - γ) ≤ X * Q := by
    have h1 : γ * (b / Nr) * x0 / (1 - γ) ≤ (b / Nr) * (1 / (1 - γ)) / (1 - γ) := by
      apply div_le_div_of_nonneg_right _ h1γ.le
      apply mul_le_mul _ hx0 hx0n (by positivity)
      nlinarith [show 0 < b / Nr by positivity]
    have e : (b / Nr) * (1 / (1 - γ)) / (1 - γ) = X * Q := by
      rw [hQdef, show X * (X / (1 - γ)) = X ^ 2 / (1 - γ) by ring, hX2]
      first | (field_simp; ring) | field_simp
    linarith
  have hB' : X * Q ≤ 1 / 10 * Q := mul_le_mul_of_nonneg_right hX1 hQ0
  have hT : Real.sqrt (b / Nr) * (γ * x1) * (3 / 2 + γ * (b / Nr) / (1 - γ))
      ≤ (Real.sqrt 2 * Q) * (3 / 2 + 1 / 100) :=
    mul_le_mul hA' (by linarith) (by positivity) (by positivity)
  have hT2 : (Real.sqrt 2 * Q) * (3 / 2 + 1 / 100) ≤ (1.415 * Q) * (3 / 2 + 1 / 100) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs2' hQ0) (by norm_num)
  have e1 : γ * Real.sqrt (b / Nr) * (3 / 2 + γ * (b / Nr) / (1 - γ)) * x1
      = Real.sqrt (b / Nr) * (γ * x1) * (3 / 2 + γ * (b / Nr) / (1 - γ)) := by ring
  have e2 : 6 / (1 - γ) * X = 6 * Q := by rw [hQdef]; ring
  rw [e1, e2]
  linarith

open Matrix in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (Phat : S → A → S → ℝ) (hPhat : FoundationsML.ReinforcementLearning.IsTransitionKernel Phat)
    (π : S → A) (β₁ : ℝ) (hβ₁ : 0 < β₁) (N : ℕ)
    (h37 : ∀ l : ℕ, (l : ℝ) ≤ Real.log (Real.exp 1 / (1 - γ)) → ∀ s,
      |((BreakingSample.Perturbed.policyMatrix Phat π - BreakingSample.Perturbed.policyMatrix P π) *ᵥ BreakingSample.Perturbed.auxV P r γ π l) s|
        ≤ Real.sqrt (β₁ / N) * Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.auxV P r γ π l) s)
          + β₁ * ‖BreakingSample.Perturbed.auxV P r γ π l‖ / N)
    (hN : 16 * Real.exp 1 ^ 2 / (1 - γ) * β₁ < N) :
    ‖fun s => BreakingSample.Perturbed.value Phat r γ π s - BreakingSample.Perturbed.value P r γ π s‖
      ≤ 6 / (1 - γ) * Real.sqrt (β₁ / (N * (1 - γ))) := by
  obtain ⟨hP, hr, hγ0, hγ1, -, -⟩ := hM
  have h1γ : 0 < 1 - γ := by linarith
  set E := Real.exp 1 with hEdef
  have hE27 : 2.7 < E := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hEpos : 0 < E := Real.exp_pos 1
  set K := Real.log (E / (1 - γ)) with hKdef
  have hK1 : 1 ≤ K := by
    rw [hKdef, Real.log_div hEpos.ne' h1γ.ne', hEdef, Real.log_exp]
    have : Real.log (1 - γ) ≤ 0 := Real.log_nonpos h1γ.le (by linarith)
    linarith
  have hNr : 0 < (N : ℝ) := lt_trans (by positivity) hN
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
  set V : ℕ → S → ℝ := fun l => BreakingSample.Perturbed.auxV P r γ π l with hVdef
  set w : ℕ → S → ℝ := fun l => Nat.casesOn l (BreakingSample.Perturbed.policyReward r π)
    (fun l => fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (V l) s)) with hwdef
  set M := BreakingSample.Perturbed.policyMatrix P π with hMdef
  set Mh := BreakingSample.Perturbed.policyMatrix Phat π with hMhdef
  have hM0 : ∀ s s', 0 ≤ M s s' := fun s s' => (hP s (π s)).1 s'
  have hM1 : ∀ s, ∑ s', M s s' = 1 := fun s => (hP s (π s)).2
  have hMh0 : ∀ s s', 0 ≤ Mh s s' := fun s s' => (hPhat s (π s)).1 s'
  have hMh1 : ∀ s, ∑ s', Mh s s' = 1 := fun s => (hPhat s (π s)).2
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
  have hVh : ∀ s, BreakingSample.Perturbed.value Phat r γ π s
      = w 0 s + γ * ∑ s', Mh s s' * BreakingSample.Perturbed.value Phat r γ π s' :=
    bs1_value_bellman Phat hPhat r γ hγ0.le hγ1 π
  have hE : ∀ l, l ≤ m → ∀ s, |∑ s', Mh s s' * V l s' - ∑ s', M s s' * V l s'|
      ≤ Real.sqrt (β₁ / N) * w (l + 1) s + β₁ / N * ‖V l‖ := by
    intro l hl s
    have hlK : (l : ℝ) ≤ Real.log (Real.exp 1 / (1 - γ)) :=
      le_trans (by exact_mod_cast hl) hmK
    have h := h37 l hlK s
    have e : ((Mh - M) *ᵥ V l) s = ∑ s', Mh s s' * V l s' - ∑ s', M s s' * V l s' := by
      rw [Matrix.sub_mulVec]; rfl
    rw [← e, show β₁ / N * ‖V l‖ = β₁ * ‖V l‖ / N by ring]
    exact h
  obtain ⟨hn2, hn3, hu⟩ := bs2_numerics γ β₁ N E hγ0 hγ1 hβ₁ hNr hE27 hN m hm1 hEm
  have hd := bs1_det M Mh hM0 hM1 hMh0 hMh1 γ hγ0 hγ1 V w
    (fun s => BreakingSample.Perturbed.value Phat r γ π s) hV hw0 hwS hVh
    (Real.sqrt (β₁ / N)) (β₁ / N) _ (Real.sqrt_nonneg _) (by positivity) (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by positivity)) m hm1 hn2 hn3 hE
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
      (fun s => bs1_norm_le (V 0) s)
      (fun s => by rw [hV 1 s]; exact congrArg (· + γ * ∑ s', M s s' * V 1 s') (hwS 0 s))
    exact bs1_norm_sq_le (V 1) _ (by positivity) (hVnn 1) hv
  have hfin := bs2_second γ β₁ N ‖V 0‖ ‖V 1‖ hγ0 hγ1 hβ₁ hNr hx0n hx1n hx0 hx1 hu
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro s
  rw [Real.norm_eq_abs]
  have hs := hd s
  have h0s : V 0 s = BreakingSample.Perturbed.value P r γ π s := congrFun hV0 s
  rw [h0s] at hs
  show |BreakingSample.Perturbed.value Phat r γ π s - BreakingSample.Perturbed.value P r γ π s| ≤ _
  linarith
