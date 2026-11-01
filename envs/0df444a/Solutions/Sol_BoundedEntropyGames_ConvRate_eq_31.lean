-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:40:43.05266+00:00
-- url     : https://prove2.me/submissions/671dbbe5-dc4c-4f22-8b2c-8bc705a5333a

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof
import Theorems.Thm_BoundedEntropyGames_ConvRate_lemma_14
import Theorems.Thm_BoundedEntropyGames_ConvRate_eq_24_25
import Theorems.Thm_BoundedEntropyGames_ConvRate_eq_29

open BoundedEntropyGames.ConvRate

theorem BGE31_sum_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : ι → κ → ℝ) : ∑ f : ι → κ, ∏ i, w i (f i) = ∏ i, ∑ b, w i b := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset κ)), Fintype.piFinset_univ]

theorem BGE31_iid_pmf {𝒳 𝒴 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒴] [DecidableEq 𝒴]
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (N : ℕ) : IsPMF (iidJoint pXY N) := by
  refine ⟨fun z => Finset.prod_nonneg fun t _ => hp.1 _, ?_⟩
  unfold iidJoint
  rw [Fintype.sum_prod_type]
  have e : ∀ xs : Fin N → 𝒳, ∑ ys : Fin N → 𝒴, ∏ t, pXY ((xs, ys).1 t, (xs, ys).2 t) =
      ∏ t, ∑ y, pXY (xs t, y) := fun xs => BGE31_sum_prod (fun t y => pXY (xs t, y))
  simp_rw [e]
  rw [BGE31_sum_prod (fun t x => ∑ y, pXY (x, y))]
  refine Finset.prod_eq_one fun t _ => ?_
  rw [← Fintype.sum_prod_type' (f := fun x y => pXY (x, y))]
  exact hp.2

theorem BGE31_ideal_pmf {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] (p₁ p₂ : 𝒜 → ℝ)
    (h₁ : IsPMF p₁) (h₂ : IsPMF p₂) (m N : ℕ) : IsPMF (idealBlock p₁ p₂ m N) := by
  refine ⟨fun a => ?_, ?_⟩
  · unfold idealBlock
    exact Finset.prod_nonneg fun t _ => by split_ifs; exact h₁.1 _; exact h₂.1 _
  · unfold idealBlock
    rw [BGE31_sum_prod (fun (t : Fin N) (b : 𝒜) => if (t : ℕ) < m then p₁ b else p₂ b)]
    refine Finset.prod_eq_one fun t _ => ?_
    split_ifs
    · exact h₁.2
    · exact h₂.2

theorem BGE31_margY_sum {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (P : 𝒳 × 𝒴 → ℝ)
    (hP : IsPMF P) : ∑ y, marginalY P y = 1 := by
  unfold marginalY
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun x y => P (x, y))]
  exact hP.2

theorem BGE31_tv_le_one {T : Type*} [Fintype T] (P Q : T → ℝ) (hP : IsPMF P) (hQ : IsPMF Q) :
    tv P Q ≤ 1 := by
  unfold tv
  have : ∑ t, |P t - Q t| ≤ ∑ t, (P t + Q t) := Finset.sum_le_sum fun t _ => by
    rw [abs_le]; constructor <;> linarith [hP.1 t, hQ.1 t]
  rw [Finset.sum_add_distrib, hP.2, hQ.2] at this
  linarith

theorem BGE31_pfXY_pmf {𝒳 𝒴 𝒜 : Type*} [Fintype 𝒳] [Fintype 𝒴] [Fintype 𝒜] [DecidableEq 𝒜]
    (P : 𝒳 × 𝒴 → ℝ) (hP : IsPMF P) (φ : 𝒳 → 𝒜) : IsPMF (pfXY P φ) := by
  refine ⟨fun z => Finset.sum_nonneg fun x _ => by split_ifs; exact hP.1 _; exact le_refl 0, ?_⟩
  unfold pfXY
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_comm]
  have : ∀ y : 𝒴, ∑ a : 𝒜, ∑ x : 𝒳, (if φ x = a then P (x, y) else 0) = ∑ x, P (x, y) := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  simp_rw [this]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun x y => P (x, y))]
  exact hP.2

theorem BGE31_prod_pmf {𝒜 𝒳 𝒴 : Type*} [Fintype 𝒜] [Fintype 𝒳] [Fintype 𝒴] (q : 𝒜 → ℝ)
    (hq : IsPMF q) (P : 𝒳 × 𝒴 → ℝ) (hP : IsPMF P) :
    IsPMF (fun z : 𝒜 × 𝒴 => q z.1 * marginalY P z.2) := by
  refine ⟨fun z => mul_nonneg (hq.1 _) (Finset.sum_nonneg fun x _ => hP.1 _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only
  simp_rw [← Finset.mul_sum, BGE31_margY_sum P hP, mul_one]
  exact hq.2

theorem solution {𝒜 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype 𝒴] [DecidableEq 𝒴]
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (r : ℝ) (hr : r ∈ Set.Ioc (0 : ℝ) 1)
    (p₁ p₂ : 𝒜 → ℝ) (hp₁ : IsPMF p₁) (hp₂ : IsPMF p₂)
    (h19 : r * shannon p₁ + (1 - r) * shannon p₂ ≤ condEntropy pXY)
    (h20 : shannon p₂ < shannon p₁) :
    ∃ γ ≥ (0 : ℝ), ∀ n f : ℕ, 1 ≤ f → f ≤ n → ∀ g ∈ Set.Icc (0 : ℝ) r,
      ∀ h ∈ Set.Ioc (0 : ℝ) 1, ∀ N N' : ℕ, N ≤ N' → (n : ℝ) / f - 1 ≤ N →
        ∃ φ : (Fin N' → 𝒳) → (Fin N → 𝒜),
          tv (pfXY (iidJoint pXY N') φ)
              (fun z => idealBlock p₁ p₂ ⌊(N : ℝ) * (r - g)⌋₊ N z.1 *
                marginalY (iidJoint pXY N') z.2)
            ≤ (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f - 1) * h *
                ((shannon p₁ - shannon p₂) * g - γ * h)) := by
  obtain ⟨γ, hγ, h29⟩ := eq_29 pXY hp r hr p₁ p₂ hp₁ hp₂ h19 h20
  refine ⟨γ, hγ, ?_⟩
  intro n f hf hfn g hg h hh N N' hNN' hN
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hg0, hgr⟩ := hg
  obtain ⟨hh0, hh1⟩ := hh
  set m := ⌊(N : ℝ) * (r - g)⌋₊ with hm
  have hNr : (N : ℝ) * (r - g) ≤ N := by
    have : r - g ≤ 1 := by linarith
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hmN : m ≤ N := Nat.floor_le_of_le hNr
  have hmle : (m : ℝ) ≤ N * (r - g) :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (by linarith))
  have hiid := BGE31_iid_pmf pXY hp N'
  have hq := BGE31_ideal_pmf p₁ p₂ hp₁ hp₂ m N
  obtain ⟨φ, hφ⟩ := (lemma_14 (iidJoint pXY N') hiid (idealBlock p₁ p₂ m N) hq).2
  refine ⟨φ, ?_⟩
  set α := 1 + h with hα
  have hαmem : α ∈ Set.Icc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hb := hφ α hαmem
  set β := shannon p₁ - shannon p₂ with hβ
  set X := β * g - γ * h with hX
  have hnf : (1 : ℝ) ≤ (n : ℝ) / f := by
    have hf' : (0 : ℝ) < f := by exact_mod_cast hf
    rw [le_div_iff₀ hf']
    have : (f : ℝ) ≤ n := by exact_mod_cast hfn
    linarith
  by_cases hX0 : X < 0
  · -- the target bound is at least 1
    have hexp : 0 ≤ -(1 / 2) * ((n : ℝ) / f - 1) * h * X := by
      have : 0 ≤ ((n : ℝ) / f - 1) * h := mul_nonneg (by linarith) hh0.le
      nlinarith
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f - 1) * h * X) :=
      Real.one_le_rpow (by norm_num) hexp
    exact le_trans (BGE31_tv_le_one _ _ (BGE31_pfXY_pmf _ hiid φ)
      (BGE31_prod_pmf _ hq _ hiid)) h1
  · push Not at hX0
    refine le_trans hb (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    -- exponent comparison
    have hαpos : 0 < α := by linarith
    have hα1 : α ≠ 1 := by linarith
    have hinvpos : 0 < 1 / α := by positivity
    have hinv1 : 1 / α ≠ 1 := by
      intro hc
      have : α = 1 := by
        field_simp at hc; linarith
      exact hα1 this
    have e24 := (eq_24_25 (𝒜 := 𝒜) (𝒳 := 𝒳) (𝒴 := 𝒴)).1 p₁ p₂ hp₁ hp₂ m N hmN (1 / α)
      hinvpos hinv1
    obtain ⟨e25a, e25b⟩ := (eq_24_25 (𝒜 := 𝒜) (𝒳 := 𝒳) (𝒴 := 𝒴)).2 pXY hp N N' hNN' α hαpos hα1
    rw [e24, e25a]
    set cR := condRenyi α pXY
    set R1 := renyi (1 / α) p₁
    set R2 := renyi (1 / α) p₂
    -- N X ≤ N cR - m R1 - (N - m) R2
    have key : (N : ℝ) * X ≤ N * cR - m * R1 - ((N : ℝ) - m) * R2 := by
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · have : m = 0 := by omega
        rw [hN0, this]; simp
      · have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
        set ρ := (m : ℝ) / N with hρ
        have hρ0 : 0 ≤ ρ := div_nonneg (Nat.cast_nonneg _) hNpos'.le
        have hρr : ρ ≤ r - g := by
          rw [hρ, div_le_iff₀ hNpos']; linarith
        have := h29 α ⟨by linarith, by linarith⟩ g ⟨hg0, hgr⟩ ρ ⟨hρ0, hρr⟩
        have hαh : α - 1 = h := by rw [hα]; ring
        rw [hαh] at this
        have hmρ : (m : ℝ) = N * ρ := by rw [hρ]; field_simp
        have := mul_le_mul_of_nonneg_left this hNpos'.le
        rw [hmρ]
        linarith only [this]
    have hL : (N : ℝ) * X + 2 ≤ N' * cR - (m * R1 + ((N : ℝ) - m) * R2) + 2 := by
      linarith only [key, e25b]
    -- 1 - 1/α ≥ h/2
    have hc : h / 2 ≤ 1 - 1 / α := by
      rw [hα]
      rw [show (1 : ℝ) - 1 / (1 + h) = h / (1 + h) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have hNX : ((n : ℝ) / f - 1) * X ≤ N * X := mul_le_mul_of_nonneg_right hN hX0
    have hL0 : 0 ≤ N' * cR - (m * R1 + ((N : ℝ) - m) * R2) + 2 := by
      have : (0 : ℝ) ≤ N * X := mul_nonneg (Nat.cast_nonneg _) hX0
      linarith
    set L := N' * cR - (m * R1 + ((N : ℝ) - m) * R2) + 2
    have s1 : h / 2 * L ≤ (1 - 1 / α) * L := mul_le_mul_of_nonneg_right hc hL0
    have s2 : h / 2 * (((n : ℝ) / f - 1) * X) ≤ h / 2 * L := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    have : -(1 / 2) * ((n : ℝ) / f - 1) * h * X = -(h / 2 * (((n : ℝ) / f - 1) * X)) := by ring
    rw [this]
    have : -(1 - 1 / α) * L = -((1 - 1 / α) * L) := by ring
    rw [this]
    linarith
