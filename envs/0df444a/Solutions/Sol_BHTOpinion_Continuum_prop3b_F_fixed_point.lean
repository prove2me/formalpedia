-- Prove2me | solution 1 for BHTOpinion.Continuum.prop3b_F_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:47:17.625622+00:00
-- url     : https://prove2.me/submissions/3c52bda6-da17-41de-b363-62dd82c236ad

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHT6P3b

open BHTOpinion.Continuum

lemma abs_opL_le (z : ℝ → ℝ) (B : ℝ) (α : ℝ)
    (h : ∀ γ ∈ I, |(if |z α - z γ| < 1 then z γ - z α else 0)| ≤ B) : |opL z α| ≤ B := by
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := I) measure_Icc_lt_top
    (f := fun γ => if |z α - z γ| < 1 then z γ - z α else 0) h
  simpa [opL, Real.volume_real_Icc] using this

lemma abs_opL_le_one (z : ℝ → ℝ) (α : ℝ) : |opL z α| ≤ 1 := by
  refine abs_opL_le z 1 α (fun γ _ => ?_)
  split_ifs with h
  · rw [abs_sub_comm]; exact h.le
  · simp

/-- A function in `F` takes finitely many values, so its gaps exceed `1 + 3ε` for some `ε > 0`. -/
lemma gap_of_F (s : ℝ → ℝ) (hs : InF s) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ α ∈ I, ∀ β ∈ I, s α = s β ∨ 1 + 3 * ε < |s α - s β| := by
  obtain ⟨C, hC⟩ := hs.1.2
  set V : Set ℝ := s '' I with hV
  have hVfin : V.Finite := by
    have hinj : Set.InjOn (fun v : ℝ => ⌊v⌋) V := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      rcases hs.2 a ha b hb with h | h
      · exact h
      · exfalso
        have h1 := Int.floor_le (s a)
        have h2 := Int.lt_floor_add_one (s a)
        have h3 := Int.floor_le (s b)
        have h4 := Int.lt_floor_add_one (s b)
        simp only at hab
        rw [hab] at h1 h2
        rw [lt_abs] at h
        rcases h with h | h <;> linarith
    refine Set.Finite.of_finite_image ?_ hinj
    refine (Set.finite_Icc (⌊-C⌋) (⌊C⌋)).subset ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have := hC a ha
    rw [abs_le] at this
    exact ⟨Int.floor_mono this.1, Int.floor_mono this.2⟩
  set D : Set ℝ := (fun p : ℝ × ℝ => |p.1 - p.2|) '' ((V ×ˢ V) ∩ {p | p.1 ≠ p.2})
  have hDfin : D.Finite := ((hVfin.prod hVfin).inter_of_left _).image _
  have hD1 : ∀ d ∈ D, 1 < d := by
    rintro _ ⟨⟨u, v⟩, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hne⟩, rfl⟩
    rcases hs.2 a ha b hb with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨c, hcmem, hcmin⟩ := Set.exists_min_image (insert 2 D) id (hDfin.insert 2)
    (Set.insert_nonempty _ _)
  have hc1 : 1 < c := by
    rcases hcmem with h | h
    · rw [h]; norm_num
    · exact hD1 c h
  refine ⟨min ((c - 1) / 4) (1 / 8), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun α hα β hβ => ?_⟩
  by_cases h : s α = s β
  · exact Or.inl h
  · right
    have hmem : |s α - s β| ∈ insert 2 D :=
      Or.inr ⟨(s α, s β), ⟨⟨⟨α, hα, rfl⟩, ⟨β, hβ, rfl⟩⟩, h⟩, rfl⟩
    have := hcmin _ hmem
    simp only [id] at this
    have := min_le_left ((c - 1) / 4) (1 / 8)
    linarith

/-- While all opinions stay within `ε` of `s`, the connection pattern is that of `s`. -/
lemma conn (s : ℝ → ℝ) (ε : ℝ) (hε4 : ε < 1 / 4)
    (hgap : ∀ α ∈ I, ∀ β ∈ I, s α = s β ∨ 1 + 3 * ε < |s α - s β|)
    (z : ℝ → ℝ) (hz : ∀ γ ∈ I, |z γ - s γ| ≤ ε) (α : ℝ) (hα : α ∈ I) (γ : ℝ) (hγ : γ ∈ I) :
    (if |z α - z γ| < 1 then z γ - z α else 0) =
      if s α = s γ then (z γ - s γ) - (z α - s α) else 0 := by
  have h1 := hz α hα
  have h2 := hz γ hγ
  rw [abs_le] at h1 h2
  rcases hgap α hα γ hγ with h | h
  · have hlt : |z α - z γ| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [if_pos hlt, if_pos h, h]; ring
  · have hne : s α ≠ s γ := by
      intro he; rw [he, sub_self, abs_zero] at h; linarith
    have hnlt : ¬ |z α - z γ| < 1 := by
      rw [not_lt]; rw [lt_abs] at h
      rcases h with h | h
      · rw [le_abs]; left; linarith
      · rw [le_abs]; right; linarith
    rw [if_neg hnlt, if_neg hne]

lemma integral_poly (ε T0 t : ℝ) (n : ℕ) :
    ∫ τ in T0..t, 2 * (ε * (2 * (τ - T0)) ^ n / n.factorial) =
      ε * (2 * (t - T0)) ^ (n + 1) / (n + 1).factorial := by
  have hf : (fun τ : ℝ => 2 * (ε * (2 * (τ - T0)) ^ n / n.factorial)) =
      fun τ => (2 * ε * 2 ^ n / n.factorial) * (τ - T0) ^ n := by
    funext τ; rw [mul_pow]; ring
  rw [hf, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x => x ^ n), integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [sub_self, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  rw [mul_pow]
  field_simp
  ring

/-- One time block: if `y` agrees with `s` at time `T0`, it agrees on `[T0, T0 + ε]`. -/
lemma block (s : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (hgap : ∀ α ∈ I, ∀ β ∈ I, s α = s β ∨ 1 + 3 * ε < |s α - s β|)
    (y : ℝ → ℝ → ℝ) (hy : IsSolution s y) (T0 : ℝ) (hT0 : 0 ≤ T0)
    (h0 : ∀ α ∈ I, y T0 α = s α) :
    ∀ t : ℝ, T0 ≤ t → t ≤ T0 + ε → ∀ α ∈ I, y t α = s α := by
  have hA : ∀ t : ℝ, T0 ≤ t → ∀ α ∈ I, y t α - s α = ∫ τ in T0..t, opL (y τ) α := by
    intro t ht α hα
    have e1 := hy.eq t (by linarith) α hα
    have e2 := hy.eq T0 hT0 α hα
    rw [h0 α hα] at e2
    have hsub := intervalIntegral.integral_interval_sub_left
      (hy.integrable t (by linarith) α hα) (hy.integrable T0 hT0 α hα)
    linarith
  have hC : ∀ t : ℝ, T0 ≤ t → t ≤ T0 + ε → ∀ α ∈ I, |y t α - s α| ≤ ε := by
    intro t ht ht' α hα
    rw [hA t ht α hα]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T0) (b := t) (C := 1)
      (f := fun τ => opL (y τ) α) (fun τ _ => by rw [Real.norm_eq_abs]; exact abs_opL_le_one _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - T0)] at this
    linarith
  have hD : ∀ n : ℕ, ∀ t : ℝ, T0 ≤ t → t ≤ T0 + ε → ∀ α ∈ I,
      |y t α - s α| ≤ ε * (2 * (t - T0)) ^ n / n.factorial := by
    intro n
    induction n with
    | zero =>
      intro t ht ht' α hα
      simpa using hC t ht ht' α hα
    | succ n ih =>
      intro t ht ht' α hα
      rw [hA t ht α hα, ← integral_poly ε T0 t n, ← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ (by
        apply Continuous.intervalIntegrable; fun_prop)
      refine Filter.Eventually.of_forall (fun τ hτ => ?_)
      have hτ1 : T0 ≤ τ := hτ.1.le
      have hτ2 : τ ≤ T0 + ε := le_trans hτ.2 ht'
      rw [Real.norm_eq_abs]
      refine abs_opL_le (y τ) _ α (fun γ hγ => ?_)
      rw [conn s ε hε4 hgap (y τ) (fun γ hγ => hC τ hτ1 hτ2 γ hγ) α hα γ hγ]
      split_ifs
      · have a1 := ih τ hτ1 hτ2 γ hγ
        have a2 := ih τ hτ1 hτ2 α hα
        calc |(y τ γ - s γ) - (y τ α - s α)| ≤ |y τ γ - s γ| + |y τ α - s α| := abs_sub _ _
          _ ≤ _ := by linarith
      · have : 0 ≤ ε * (2 * (τ - T0)) ^ n / n.factorial := by
          apply div_nonneg
          · apply mul_nonneg hε.le; apply pow_nonneg; linarith
          · positivity
        simp; linarith
  intro t ht ht' α hα
  have hlim : Tendsto (fun n : ℕ => ε * ((2 * (t - T0)) ^ n / n.factorial)) atTop (𝓝 (ε * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop _).const_mul ε
  have hle : |y t α - s α| ≤ ε * 0 := by
    refine ge_of_tendsto' hlim (fun n => ?_)
    rw [← mul_div_assoc]; exact hD n t ht ht' α hα
  have : |y t α - s α| = 0 := le_antisymm (by simpa using hle) (abs_nonneg _)
  linarith [abs_eq_zero.mp this]

end BHT6P3b

open BHTOpinion.Continuum in
theorem solution (s : ℝ → ℝ) (hs : InF s) : IsFixedPoint s := by
  have hopL0 : ∀ α ∈ I, opL s α = 0 := by
    intro α hα
    unfold opL
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro γ hγ
    rcases hs.2 α hα γ hγ with h | h
    · simp [h]
    · have : ¬ |s α - s γ| < 1 := by linarith
      simp [this]
  have hmon : Monotone (fun a : I => s a) := fun a b hab => hs.1.1 a.2 b.2 hab
  have hmeas : Measurable (fun a : I => s a) := hmon.measurable
  have hY : InY s := ⟨hmeas, hs.1.2⟩
  refine ⟨hs.1, ⟨hmeas.comp measurable_fst, fun _ _ => hY, fun t _ α hα => ?_,
    fun t _ α hα => ?_⟩, ?_⟩
  · show IntervalIntegrable (fun _ : ℝ => opL s α) volume 0 t
    exact intervalIntegrable_const
  · show s α = s α + ∫ _ in (0 : ℝ)..t, opL s α
    rw [hopL0 α hα]; simp
  · intro y hy t ht α hα
    obtain ⟨ε, hε, hε4, hgap⟩ := BHT6P3b.gap_of_F s hs
    have hk : ∀ k : ℕ, ∀ α ∈ I, y (k * ε) α = s α := by
      intro k
      induction k with
      | zero =>
        intro α hα
        have := hy.eq 0 le_rfl α hα
        simpa using this
      | succ k ih =>
        intro α hα
        have hk0 : (0 : ℝ) ≤ k * ε := by positivity
        have := BHT6P3b.block s ε hε hε4 hgap y hy (k * ε) hk0 ih ((k + 1 : ℕ) * ε)
          (by push_cast; nlinarith) (by push_cast; nlinarith) α hα
        exact this
    set k := ⌊t / ε⌋₊
    have h1 : (k : ℝ) ≤ t / ε := Nat.floor_le (div_nonneg ht hε.le)
    have h2 : t / ε < k + 1 := Nat.lt_floor_add_one _
    have h1' : (k : ℝ) * ε ≤ t := by rwa [le_div_iff₀ hε] at h1
    have h2' : t < (k + 1) * ε := by rwa [div_lt_iff₀ hε] at h2
    have hk0 : (0 : ℝ) ≤ k * ε := by positivity
    exact BHT6P3b.block s ε hε hε4 hgap y hy (k * ε) hk0 (hk k) t h1' (by linarith) α hα
