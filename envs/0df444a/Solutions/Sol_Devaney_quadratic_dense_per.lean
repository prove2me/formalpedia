-- Prove2me | solution 1 for Devaney.quadratic_dense_per
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T00:21:57.889356+00:00
-- url     : https://prove2.me/submissions/d314a5d4-11bf-49d7-8a2d-b10800af0289

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Dev72

open Devaney Devaney.Sigma2

/-- `r = √(1 - 4/μ)`, the half-width of the gap removed from the unit interval. -/
noncomputable def rad (μ : ℝ) : ℝ := Real.sqrt (1 - 4 / μ)

/-- The right endpoint of the left piece `I₀`. -/
noncomputable def pm (μ : ℝ) : ℝ := (1 - rad μ) / 2

/-- The left endpoint of the right piece `I₁`. -/
noncomputable def pp (μ : ℝ) : ℝ := (1 + rad μ) / 2

/-- The expansion constant `λ = μ r = √(μ² - 4μ)`. -/
noncomputable def lam (μ : ℝ) : ℝ := μ * rad μ

variable {μ : ℝ} {b : Fin 2} {s : Sigma2} {n : ℕ}

theorem four_lt (hμ : 2 + Real.sqrt 5 < μ) : 4 < μ := by
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    have : Real.sqrt 4 < Real.sqrt 5 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq] <;> norm_num] using this
  linarith

theorem rad_sq (hμ : 2 + Real.sqrt 5 < μ) : rad μ ^ 2 = 1 - 4 / μ := by
  have h4 := four_lt hμ
  have : (0:ℝ) ≤ 1 - 4 / μ := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  exact Real.sq_sqrt this

theorem rad_pos (hμ : 2 + Real.sqrt 5 < μ) : 0 < rad μ := by
  have h4 := four_lt hμ
  apply Real.sqrt_pos.2
  rw [sub_pos, div_lt_one (by linarith)]; linarith

theorem rad_lt_one (hμ : 2 + Real.sqrt 5 < μ) : rad μ < 1 := by
  have h4 := four_lt hμ
  have hsq := rad_sq hμ
  have hpos := rad_pos hμ
  have hq : (0:ℝ) < 4 / μ := by positivity
  have hlt : rad μ ^ 2 < 1 := by rw [hsq]; linarith
  nlinarith [hlt, hpos]

/-- The cleared form of `r² = 1 - 4/μ`. -/
theorem mul_rad_sq (hμ : 2 + Real.sqrt 5 < μ) : μ * rad μ ^ 2 = μ - 4 := by
  have h4 := four_lt hμ
  have hμ0 : μ ≠ 0 := by linarith
  rw [rad_sq hμ]
  field_simp

theorem lam_gt_one (hμ : 2 + Real.sqrt 5 < μ) : 1 < lam μ := by
  have h4 := four_lt hμ
  have hsq := rad_sq hμ
  have hpos := rad_pos hμ
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5nn : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hgt : Real.sqrt 5 < μ - 2 := by linarith
  have h5lt : (5:ℝ) < (μ - 2) ^ 2 := by nlinarith [hs5, hs5nn, hgt]
  have hkey : 1 < μ ^ 2 - 4 * μ := by nlinarith [h5lt]
  have hlamsq : lam μ ^ 2 = μ ^ 2 - 4 * μ := by
    unfold lam
    rw [mul_pow]
    linear_combination μ * mul_rad_sq hμ
  have hlampos : 0 < lam μ := mul_pos (by linarith) hpos
  nlinarith [hlamsq, hkey, hlampos]

theorem pm_lt_half (hμ : 2 + Real.sqrt 5 < μ) : pm μ < 1 / 2 := by
  have := rad_pos hμ; unfold pm; linarith

theorem half_lt_pp (hμ : 2 + Real.sqrt 5 < μ) : 1 / 2 < pp μ := by
  have := rad_pos hμ; unfold pp; linarith

theorem pm_pos (hμ : 2 + Real.sqrt 5 < μ) : 0 < pm μ := by
  have := rad_lt_one hμ; unfold pm; linarith

theorem pp_lt_one (hμ : 2 + Real.sqrt 5 < μ) : pp μ < 1 := by
  have := rad_lt_one hμ; unfold pp; linarith

/-- The two roots of `μ x (1 - x) = 1`. -/
theorem quad_pm (hμ : 2 + Real.sqrt 5 < μ) : quadratic μ (pm μ) = 1 := by
  have hsq2 := mul_rad_sq hμ
  unfold quadratic pm
  linear_combination (-1/4 : ℝ) * hsq2

theorem quad_pp (hμ : 2 + Real.sqrt 5 < μ) : quadratic μ (pp μ) = 1 := by
  have hsq2 := mul_rad_sq hμ
  unfold quadratic pp
  linear_combination (-1/4 : ℝ) * hsq2


/-- The left piece `I₀ = [0, p⁻]`. -/
def I0 (μ : ℝ) : Set ℝ := Set.Icc 0 (pm μ)

/-- The right piece `I₁ = [p⁺, 1]`. -/
def I1 (μ : ℝ) : Set ℝ := Set.Icc (pp μ) 1

theorem I0_subset (hμ : 2 + Real.sqrt 5 < μ) : I0 μ ⊆ Set.Icc (0:ℝ) 1 := by
  have h1 := pm_lt_half hμ
  exact Set.Icc_subset_Icc le_rfl (by linarith)

theorem I1_subset (hμ : 2 + Real.sqrt 5 < μ) : I1 μ ⊆ Set.Icc (0:ℝ) 1 := by
  have h1 := half_lt_pp hμ
  exact Set.Icc_subset_Icc (by linarith) le_rfl

/-- The factorization `1 - μ x (1 - x) = μ (x - p⁻)(x - p⁺)`. -/
theorem one_sub_quadratic (hμ : 2 + Real.sqrt 5 < μ) (x : ℝ) :
    μ * (x - pm μ) * (x - pp μ) = 1 - quadratic μ x := by
  have hsq2 := mul_rad_sq hμ
  unfold quadratic pm pp
  linear_combination (-1/4 : ℝ) * hsq2

/-- A point of the unit interval whose image is again in the unit interval lies in one of the
two pieces. -/
theorem mem_pieces (hμ : 2 + Real.sqrt 5 < μ) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hfx : quadratic μ x ≤ 1) : x ∈ I0 μ ∪ I1 μ := by
  have h4 := four_lt hμ
  have hfac := one_sub_quadratic hμ x
  have hnn : 0 ≤ μ * (x - pm μ) * (x - pp μ) := by rw [hfac]; linarith
  by_contra hcon
  simp only [Set.mem_union, I0, I1, Set.mem_Icc, not_or, not_and_or, not_le] at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hxpm : pm μ < x := by
    rcases h0 with h | h
    · exact absurd hx.1 (by linarith)
    · exact h
  have hxpp : x < pp μ := by
    rcases h1 with h | h
    · exact h
    · exact absurd hx.2 (by linarith)
  have hneg : μ * (x - pm μ) * (x - pp μ) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by linarith) (by linarith)) (by linarith)
  linarith

theorem lambda_mem_unitI {x : ℝ} (hx : x ∈ Lambda μ) (n : ℕ) :
    (quadratic μ)^[n] x ∈ Set.Icc (0:ℝ) 1 := hx n

theorem lambda_iterate {x : ℝ} (hx : x ∈ Lambda μ) (n : ℕ) :
    (quadratic μ)^[n] x ∈ Lambda μ := by
  intro m
  have : (quadratic μ)^[m] ((quadratic μ)^[n] x) = (quadratic μ)^[m + n] x := by
    rw [Function.iterate_add_apply]
  rw [this]
  exact hx (m + n)

theorem lambda_subset_pieces (hμ : 2 + Real.sqrt 5 < μ) : Lambda μ ⊆ I0 μ ∪ I1 μ := by
  intro x hx
  refine mem_pieces hμ (hx 0) ?_
  have := hx 1
  simpa using this.2


theorem continuous_quadratic : Continuous (quadratic μ) := by
  unfold quadratic
  fun_prop

/-- On either piece the map expands distances by the factor `λ`. -/
theorem expand (hμ : 2 + Real.sqrt 5 < μ) {x y : ℝ}
    (h : (x ∈ I0 μ ∧ y ∈ I0 μ) ∨ (x ∈ I1 μ ∧ y ∈ I1 μ)) :
    lam μ * |x - y| ≤ |quadratic μ x - quadratic μ y| := by
  have h4 := four_lt hμ
  have hr := rad_pos hμ
  have hgap : rad μ ≤ |1 - x - y| := by
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hx2 : x ≤ pm μ := hx.2
      have hy2 : y ≤ pm μ := hy.2
      unfold pm at hx2 hy2
      have hle : rad μ ≤ 1 - x - y := by linarith
      calc rad μ ≤ 1 - x - y := hle
        _ ≤ |1 - x - y| := le_abs_self _
    · have hx1 : pp μ ≤ x := hx.1
      have hy1 : pp μ ≤ y := hy.1
      unfold pp at hx1 hy1
      have hle : rad μ ≤ -(1 - x - y) := by linarith
      calc rad μ ≤ -(1 - x - y) := hle
        _ ≤ |1 - x - y| := neg_le_abs _
  have hfac : quadratic μ x - quadratic μ y = μ * (x - y) * (1 - x - y) := by
    unfold quadratic; ring
  rw [hfac, abs_mul, abs_mul, abs_of_pos (show (0:ℝ) < μ by linarith)]
  have habs : (0:ℝ) ≤ |x - y| := abs_nonneg _
  have : lam μ * |x - y| = μ * rad μ * |x - y| := rfl
  rw [this]
  calc μ * rad μ * |x - y| = μ * |x - y| * rad μ := by ring
    _ ≤ μ * |x - y| * |1 - x - y| := by
        apply mul_le_mul_of_nonneg_left hgap
        positivity

/-- `F` maps the left piece onto the unit interval. -/
theorem covers_I0 (hμ : 2 + Real.sqrt 5 < μ) : Set.Icc (0:ℝ) 1 ⊆ quadratic μ '' I0 μ := by
  have hpm := pm_pos hμ
  have h0 : quadratic μ 0 = 0 := by unfold quadratic; ring
  have h1 : quadratic μ (pm μ) = 1 := quad_pm hμ
  have := intermediate_value_Icc (le_of_lt hpm)
    (continuous_quadratic.continuousOn : ContinuousOn (quadratic μ) (Set.Icc 0 (pm μ)))
  rwa [h0, h1] at this

/-- `F` maps the right piece onto the unit interval. -/
theorem covers_I1 (hμ : 2 + Real.sqrt 5 < μ) : Set.Icc (0:ℝ) 1 ⊆ quadratic μ '' I1 μ := by
  have hpp := pp_lt_one hμ
  have h0 : quadratic μ 1 = 0 := by unfold quadratic; ring
  have h1 : quadratic μ (pp μ) = 1 := quad_pp hμ
  have := intermediate_value_Icc' (le_of_lt hpp)
    (continuous_quadratic.continuousOn : ContinuousOn (quadratic μ) (Set.Icc (pp μ) 1))
  rwa [h0, h1] at this

theorem lambda_isClosed : IsClosed (Lambda μ) := by
  have : Lambda μ = ⋂ n : ℕ, (quadratic μ)^[n] ⁻¹' (Set.Icc (0:ℝ) 1) := by
    ext x
    simp [Lambda, unitI, Set.mem_iInter]
  rw [this]
  exact isClosed_iInter fun n =>
    (isClosed_Icc).preimage (continuous_quadratic.iterate n)

theorem lambda_isCompact : IsCompact (Lambda μ) :=
  isCompact_Icc.of_isClosed_subset lambda_isClosed (fun x hx => hx 0)


/-- The piece named by a symbol. -/
def pieceOf (μ : ℝ) (b : Fin 2) : Set ℝ := if b = 0 then I0 μ else I1 μ

theorem pieceOf_subset (hμ : 2 + Real.sqrt 5 < μ) (b : Fin 2) :
    pieceOf μ b ⊆ Set.Icc (0:ℝ) 1 := by
  unfold pieceOf
  split
  · exact I0_subset hμ
  · exact I1_subset hμ

theorem pieceOf_isClosed : IsClosed (pieceOf μ b) := by
  unfold pieceOf I0 I1
  split <;> exact isClosed_Icc

theorem pieceOf_nonempty (hμ : 2 + Real.sqrt 5 < μ) (b : Fin 2) : (pieceOf μ b).Nonempty := by
  unfold pieceOf I0 I1
  split
  · exact ⟨0, Set.left_mem_Icc.2 (le_of_lt (pm_pos hμ))⟩
  · exact ⟨1, Set.right_mem_Icc.2 (le_of_lt (pp_lt_one hμ))⟩

theorem covers (hμ : 2 + Real.sqrt 5 < μ) (b : Fin 2) :
    Set.Icc (0:ℝ) 1 ⊆ quadratic μ '' pieceOf μ b := by
  unfold pieceOf
  split
  · exact covers_I0 hμ
  · exact covers_I1 hμ

/-- On `Λ` the itinerary digit records which piece the iterate lies in. -/
theorem mem_pieceOf_itinerary (hμ : 2 + Real.sqrt 5 < μ) {x : ℝ} (hx : x ∈ Lambda μ) (n : ℕ) :
    (quadratic μ)^[n] x ∈ pieceOf μ (itinerary μ x n) := by
  have hp := lambda_subset_pieces hμ (lambda_iterate hx n)
  have h1 := pm_lt_half hμ
  have h2 := half_lt_pp hμ
  rcases hp with h0 | h1'
  · have hle : (quadratic μ)^[n] x ≤ 1 / 2 := le_trans h0.2 (le_of_lt h1)
    have : itinerary μ x n = 0 := by simp only [itinerary]; exact if_pos hle
    rw [this]
    simpa [pieceOf] using h0
  · have hgt : ¬ ((quadratic μ)^[n] x ≤ 1 / 2) := by
      have := h1'.1
      linarith
    have : itinerary μ x n = 1 := by simp only [itinerary]; exact if_neg hgt
    rw [this]
    simpa [pieceOf] using h1'

/-- The itinerary is determined by which pieces the orbit visits. -/
theorem itinerary_eq_of_mem (hμ : 2 + Real.sqrt 5 < μ) {x : ℝ} {s : Sigma2}
    (h : ∀ n, (quadratic μ)^[n] x ∈ pieceOf μ (s n)) : itinerary μ x = s := by
  funext n
  have hn := h n
  have h1 := pm_lt_half hμ
  have h2 := half_lt_pp hμ
  rcases Fin.exists_fin_two.1 ⟨s n, rfl⟩ with _
  by_cases hb : s n = 0
  · rw [hb] at hn ⊢
    have : (quadratic μ)^[n] x ≤ 1 / 2 := by
      have := (show (quadratic μ)^[n] x ∈ I0 μ by simpa [pieceOf] using hn).2
      linarith
    simp only [itinerary]; exact if_pos this
  · have hb1 : s n = 1 := by omega
    rw [hb1] at hn ⊢
    have : ¬ ((quadratic μ)^[n] x ≤ 1 / 2) := by
      have := (show (quadratic μ)^[n] x ∈ I1 μ by simpa [pieceOf, hb1] using hn).1
      linarith
    simp only [itinerary]; exact if_neg this


/-- Expansion along an orbit with a common itinerary. -/
theorem iterate_expand (hμ : 2 + Real.sqrt 5 < μ) {x y : ℝ} (hx : x ∈ Lambda μ) (hy : y ∈ Lambda μ)
    (h : itinerary μ x = itinerary μ y) (n : ℕ) :
    lam μ ^ n * |x - y| ≤ |(quadratic μ)^[n] x - (quadratic μ)^[n] y| := by
  have hlam : 0 < lam μ := lt_trans one_pos (lam_gt_one hμ)
  induction n with
  | zero => simp
  | succ n ih =>
    have hpx := mem_pieceOf_itinerary hμ hx n
    have hpy := mem_pieceOf_itinerary hμ hy n
    rw [h] at hpx
    have hsame : ((quadratic μ)^[n] x ∈ I0 μ ∧ (quadratic μ)^[n] y ∈ I0 μ)
        ∨ ((quadratic μ)^[n] x ∈ I1 μ ∧ (quadratic μ)^[n] y ∈ I1 μ) := by
      by_cases hb : itinerary μ y n = 0
      · rw [hb] at hpx hpy
        exact Or.inl ⟨by simpa [pieceOf] using hpx, by simpa [pieceOf] using hpy⟩
      · have hb1 : itinerary μ y n = 1 := by omega
        rw [hb1] at hpx hpy
        exact Or.inr ⟨by simpa [pieceOf] using hpx, by simpa [pieceOf] using hpy⟩
    have hstep := expand hμ hsame
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc lam μ ^ (n + 1) * |x - y| = lam μ * (lam μ ^ n * |x - y|) := by ring
      _ ≤ lam μ * |(quadratic μ)^[n] x - (quadratic μ)^[n] y| :=
          mul_le_mul_of_nonneg_left ih (le_of_lt hlam)
      _ ≤ |quadratic μ ((quadratic μ)^[n] x) - quadratic μ ((quadratic μ)^[n] y)| := hstep

theorem itinerary_injOn (hμ : 2 + Real.sqrt 5 < μ) : Set.InjOn (itinerary μ) (Lambda μ) := by
  intro x hx y hy h
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |x - y|) (lam_gt_one hμ)
  have hbound : |(quadratic μ)^[n] x - (quadratic μ)^[n] y| ≤ 1 := by
    have hx1 := hx n
    have hy1 := hy n
    rw [abs_le]
    constructor <;> [linarith [hx1.1, hx1.2, hy1.1, hy1.2]; linarith [hx1.1, hx1.2, hy1.1, hy1.2]]
  have hexp := iterate_expand hμ hx hy h n
  have : 1 < lam μ ^ n * |x - y| := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  linarith


/-- A finite covering chain: every finite word is realized by some orbit. -/
theorem exists_finite_orbit (hμ : 2 + Real.sqrt 5 < μ) (s : Sigma2) (n : ℕ) :
    ∃ x, ∀ i ≤ n, (quadratic μ)^[i] x ∈ pieceOf μ (s i) := by
  induction n generalizing s with
  | zero =>
    obtain ⟨x, hx⟩ := pieceOf_nonempty hμ (s 0)
    exact ⟨x, fun i hi => by interval_cases i; simpa using hx⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (fun i => s (i + 1))
    have hy0 : y ∈ Set.Icc (0:ℝ) 1 := pieceOf_subset hμ _ (by simpa using hy 0 (Nat.zero_le n))
    obtain ⟨x, hx, hxy⟩ := covers hμ (s 0) hy0
    refine ⟨x, fun i hi => ?_⟩
    match i with
    | 0 => simpa using hx
    | (j + 1) =>
      have := hy j (by omega)
      rw [Function.iterate_succ_apply, hxy]
      exact this

/-- The compact sets cutting out the orbits with a prescribed finite itinerary. -/
def approx (μ : ℝ) (s : Sigma2) (n : ℕ) : Set ℝ :=
  {x | ∀ i ≤ n, (quadratic μ)^[i] x ∈ pieceOf μ (s i)}

theorem approx_isClosed : IsClosed (approx μ s n) := by
  have : approx μ s n = ⋂ i ∈ Finset.range (n + 1),
      (quadratic μ)^[i] ⁻¹' pieceOf μ (s i) := by
    ext x
    simp only [approx, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
    constructor
    · intro h i hi; exact h i (by omega)
    · intro h i hi; exact h i (by omega)
  rw [this]
  exact isClosed_biInter fun i _ => pieceOf_isClosed.preimage (continuous_quadratic.iterate i)

theorem approx_antitone : approx μ s (n + 1) ⊆ approx μ s n :=
  fun x hx i hi => hx i (by omega)

theorem approx_subset_unitI (hμ : 2 + Real.sqrt 5 < μ) : approx μ s n ⊆ Set.Icc (0:ℝ) 1 := by
  intro x hx
  have := hx 0 (Nat.zero_le n)
  simpa using pieceOf_subset hμ _ this

theorem itinerary_surjOn (hμ : 2 + Real.sqrt 5 < μ) (s : Sigma2) :
    ∃ x ∈ Lambda μ, itinerary μ x = s := by
  have hne : ∀ n, (approx μ s n).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := exists_finite_orbit hμ s n
    exact ⟨x, hx⟩
  have hcl : ∀ n, IsClosed (approx μ s n) := fun n => approx_isClosed
  have hcp : ∀ n, IsCompact (approx μ s n) := fun n =>
    isCompact_Icc.of_isClosed_subset (hcl n) (approx_subset_unitI hμ)
  have hanti : ∀ n, approx μ s (n + 1) ⊆ approx μ s n := fun n => approx_antitone
  have hinter : (⋂ n, approx μ s n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hanti hne (hcp 0) hcl
  obtain ⟨x, hx⟩ := hinter
  simp only [Set.mem_iInter] at hx
  have hall : ∀ n, (quadratic μ)^[n] x ∈ pieceOf μ (s n) := fun n => hx n n le_rfl
  refine ⟨x, fun n => ?_, itinerary_eq_of_mem hμ hall⟩
  exact pieceOf_subset hμ _ (hall n)


/-- On the unit interval the quadratic map is Lipschitz with constant `μ`. -/
theorem lipschitz (hμ : 2 + Real.sqrt 5 < μ) {u v : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    |quadratic μ u - quadratic μ v| ≤ μ * |u - v| := by
  have h4 := four_lt hμ
  have hfac : quadratic μ u - quadratic μ v = μ * (u - v) * (1 - u - v) := by
    unfold quadratic; ring
  have hle : |1 - u - v| ≤ 1 := by
    rw [abs_le]
    constructor <;> [linarith [hu.1, hu.2, hv.1, hv.2]; linarith [hu.1, hu.2, hv.1, hv.2]]
  rw [hfac, abs_mul, abs_mul, abs_of_pos (show (0:ℝ) < μ by linarith)]
  have : μ * |u - v| * |1 - u - v| ≤ μ * |u - v| * 1 :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  linarith

theorem iterate_lipschitz (hμ : 2 + Real.sqrt 5 < μ) {x y : ℝ}
    (hx : x ∈ Lambda μ) (hy : y ∈ Lambda μ) (n : ℕ) :
    |(quadratic μ)^[n] x - (quadratic μ)^[n] y| ≤ μ ^ n * |x - y| := by
  have h4 := four_lt hμ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc |quadratic μ ((quadratic μ)^[n] x) - quadratic μ ((quadratic μ)^[n] y)|
        ≤ μ * |(quadratic μ)^[n] x - (quadratic μ)^[n] y| := lipschitz hμ (hx n) (hy n)
      _ ≤ μ * (μ ^ n * |x - y|) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = μ ^ (n + 1) * |x - y| := by ring

/-- Two points of `Λ` whose itineraries first differ at index `i` are at least `r / μ^i`
apart. -/
theorem sep_of_digit_ne (hμ : 2 + Real.sqrt 5 < μ) {x y : ℝ}
    (hx : x ∈ Lambda μ) (hy : y ∈ Lambda μ) {i : ℕ} (hne : itinerary μ x i ≠ itinerary μ y i) :
    rad μ ≤ μ ^ i * |x - y| := by
  have hpx := mem_pieceOf_itinerary hμ hx i
  have hpy := mem_pieceOf_itinerary hμ hy i
  have hgap : rad μ ≤ |(quadratic μ)^[i] x - (quadratic μ)^[i] y| := by
    by_cases hb : itinerary μ x i = 0
    · have hb' : itinerary μ y i = 1 := by omega
      rw [hb] at hpx; rw [hb'] at hpy
      have h1 : (quadratic μ)^[i] x ≤ pm μ := (show _ ∈ I0 μ by simpa [pieceOf] using hpx).2
      have h2 : pp μ ≤ (quadratic μ)^[i] y := (show _ ∈ I1 μ by simpa [pieceOf] using hpy).1
      have : rad μ ≤ -((quadratic μ)^[i] x - (quadratic μ)^[i] y) := by
        unfold pm at h1; unfold pp at h2; linarith
      calc rad μ ≤ _ := this
        _ ≤ |(quadratic μ)^[i] x - (quadratic μ)^[i] y| := neg_le_abs _
    · have hb1 : itinerary μ x i = 1 := by omega
      have hb' : itinerary μ y i = 0 := by omega
      rw [hb1] at hpx; rw [hb'] at hpy
      have h1 : pp μ ≤ (quadratic μ)^[i] x := (show _ ∈ I1 μ by simpa [pieceOf] using hpx).1
      have h2 : (quadratic μ)^[i] y ≤ pm μ := (show _ ∈ I0 μ by simpa [pieceOf] using hpy).2
      have : rad μ ≤ (quadratic μ)^[i] x - (quadratic μ)^[i] y := by
        unfold pp at h1; unfold pm at h2; linarith
      calc rad μ ≤ _ := this
        _ ≤ |(quadratic μ)^[i] x - (quadratic μ)^[i] y| := le_abs_self _
  exact le_trans hgap (iterate_lipschitz hμ hx hy i)




theorem dist_eq (s t : Sigma2) : dist s t = ∑' i, distTerm s t i := rfl

theorem entry_ne (s t : Sigma2) (i : ℕ) (h : s i ≠ t i) : s.entry i ≠ t.entry i := fun he =>
  h (Fin.ext (Nat.cast_injective he))

theorem distTerm_eq_zero (s t : Sigma2) (i : ℕ) (h : s i = t i) : distTerm s t i = 0 := by
  simp [distTerm, entry, h]

theorem dist_le_of_agree (s t : Sigma2) (n : ℕ) (h : ∀ i ≤ n, s i = t i) :
    dist s t ≤ 1 / 2 ^ n := by
  have hzero : ∑ i ∈ Finset.range (n + 1), distTerm s t i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp [distTerm, entry, h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hsplit := (summable_distTerm s t).sum_add_tsum_nat_add (n + 1)
  rw [hzero, zero_add] at hsplit
  have hsummable : Summable (fun i => distTerm s t (i + (n + 1))) :=
    (summable_distTerm s t).comp_injective (add_left_injective (n + 1))
  have hg : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + (n + 1))) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).mul_right ((1/2 : ℝ) ^ (n + 1))
  have hshow : dist s t = ∑' i, distTerm s t (i + (n + 1)) := by
    show (∑' i, distTerm s t i) = _
    rw [← hsplit]
  rw [hshow]
  calc ∑' i, distTerm s t (i + (n + 1))
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (n + 1)) :=
        Summable.tsum_le_tsum (fun i => distTerm_le s t _) hsummable hg
    _ = 1 / 2 ^ n := by
        rw [show (fun i : ℕ => (1/2:ℝ) ^ (i + (n+1))) = fun i : ℕ => (1/2:ℝ) ^ (n+1) * (1/2)^i from
          by funext i; rw [pow_add, mul_comm]]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        rw [pow_succ]
        norm_num
        rw [← inv_pow]
        ring

theorem exists_half_pow_lt {r : ℝ} (hr : 0 < r) : ∃ n : ℕ, (1 : ℝ) / 2 ^ n < r := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1/2:ℝ) < 1)
  exact ⟨n, by rwa [div_pow, one_pow] at hn⟩


/-- The itinerary map is uniformly continuous on `Λ`: two points closer than `r / μ^n` have
the same first `n+1` symbols. -/
theorem itinerary_continuous (hμ : 2 + Real.sqrt 5 < μ) :
    Continuous (fun x : Lambda μ => itinerary μ x.1) := by
  have h4 := four_lt hμ
  have hr := rad_pos hμ
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨n, hn⟩ := exists_half_pow_lt hε
  refine ⟨rad μ / μ ^ n, by positivity, ?_⟩
  intro a hab
  have habs : |a.1 - b.1| < rad μ / μ ^ n := by
    have : dist a b = |a.1 - b.1| := by
      rw [Subtype.dist_eq, Real.dist_eq]
    rwa [this] at hab
  have hagree : ∀ i ≤ n, itinerary μ a.1 i = itinerary μ b.1 i := by
    intro i hi
    by_contra hne
    have hsep := sep_of_digit_ne hμ a.2 b.2 hne
    have hmono : μ ^ i ≤ μ ^ n := pow_le_pow_right₀ (by linarith) hi
    have hpn : (0:ℝ) < μ ^ n := by positivity
    have h1 : μ ^ i * |a.1 - b.1| ≤ μ ^ n * |a.1 - b.1| :=
      mul_le_mul_of_nonneg_right hmono (abs_nonneg _)
    have h2 : μ ^ n * |a.1 - b.1| < μ ^ n * (rad μ / μ ^ n) :=
      mul_lt_mul_of_pos_left habs hpn
    rw [mul_div_cancel₀ _ (ne_of_gt hpn)] at h2
    linarith
  exact lt_of_le_of_lt (dist_le_of_agree _ _ n hagree) hn

/-- Theorem 7.2: for `μ > 2 + √5` the itinerary map is a homeomorphism from `Λ` to `Σ₂`. -/
theorem itinerary_homeomorph (hμ : 2 + Real.sqrt 5 < μ) :
    ∃ h : (Lambda μ) ≃ₜ Sigma2, ∀ x : Lambda μ, h x = itinerary μ x.1 := by
  have hcompact : CompactSpace (Lambda μ) := isCompact_iff_compactSpace.1 lambda_isCompact
  have hinj : Function.Injective (fun x : Lambda μ => itinerary μ x.1) := by
    intro a b hab
    exact Subtype.ext (itinerary_injOn hμ a.2 b.2 hab)
  have hsurj : Function.Surjective (fun x : Lambda μ => itinerary μ x.1) := by
    intro s
    obtain ⟨x, hx, hxs⟩ := itinerary_surjOn hμ s
    exact ⟨⟨x, hx⟩, hxs⟩
  let e : Lambda μ ≃ Sigma2 := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := e) (itinerary_continuous hμ), fun x => rfl⟩


/-- Expansion needs only agreement of the first `n` symbols. -/
theorem iterate_expand' (hμ : 2 + Real.sqrt 5 < μ) {x y : ℝ} (hx : x ∈ Lambda μ) (hy : y ∈ Lambda μ)
    (n : ℕ) (h : ∀ i < n, itinerary μ x i = itinerary μ y i) :
    lam μ ^ n * |x - y| ≤ |(quadratic μ)^[n] x - (quadratic μ)^[n] y| := by
  have hlam : 0 < lam μ := lt_trans one_pos (lam_gt_one hμ)
  induction n with
  | zero => simp
  | succ n ih =>
    have ihh := ih (fun i hi => h i (by omega))
    have hpx := mem_pieceOf_itinerary hμ hx n
    have hpy := mem_pieceOf_itinerary hμ hy n
    rw [h n (by omega)] at hpx
    have hsame : ((quadratic μ)^[n] x ∈ I0 μ ∧ (quadratic μ)^[n] y ∈ I0 μ)
        ∨ ((quadratic μ)^[n] x ∈ I1 μ ∧ (quadratic μ)^[n] y ∈ I1 μ) := by
      by_cases hb : itinerary μ y n = 0
      · rw [hb] at hpx hpy
        exact Or.inl ⟨by simpa [pieceOf] using hpx, by simpa [pieceOf] using hpy⟩
      · have hb1 : itinerary μ y n = 1 := by omega
        rw [hb1] at hpx hpy
        exact Or.inr ⟨by simpa [pieceOf] using hpx, by simpa [pieceOf] using hpy⟩
    have hstep := expand hμ hsame
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc lam μ ^ (n + 1) * |x - y| = lam μ * (lam μ ^ n * |x - y|) := by ring
      _ ≤ lam μ * |(quadratic μ)^[n] x - (quadratic μ)^[n] y| :=
          mul_le_mul_of_nonneg_left ihh (le_of_lt hlam)
      _ ≤ |quadratic μ ((quadratic μ)^[n] x) - quadratic μ ((quadratic μ)^[n] y)| := hstep

/-- Agreement of the first `n` symbols forces closeness. -/
theorem close_of_agree (hμ : 2 + Real.sqrt 5 < μ) {x y : ℝ} (hx : x ∈ Lambda μ) (hy : y ∈ Lambda μ)
    (n : ℕ) (h : ∀ i < n, itinerary μ x i = itinerary μ y i) :
    |x - y| ≤ 1 / lam μ ^ n := by
  have hlam : 0 < lam μ := lt_trans one_pos (lam_gt_one hμ)
  have hpow : (0:ℝ) < lam μ ^ n := by positivity
  have hexp := iterate_expand' hμ hx hy n h
  have hb : |(quadratic μ)^[n] x - (quadratic μ)^[n] y| ≤ 1 := by
    have hx1 := hx n
    have hy1 := hy n
    rw [abs_le]
    constructor <;> [linarith [hx1.1, hx1.2, hy1.1, hy1.2]; linarith [hx1.1, hx1.2, hy1.1, hy1.2]]
  rw [le_div_iff₀ hpow]
  calc |x - y| * lam μ ^ n = lam μ ^ n * |x - y| := by ring
    _ ≤ |(quadratic μ)^[n] x - (quadratic μ)^[n] y| := hexp
    _ ≤ 1 := hb

theorem exists_pow_lam_lt (hμ : 2 + Real.sqrt 5 < μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 1 / lam μ ^ n < ε := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ε) (lam_gt_one hμ)
  refine ⟨n, ?_⟩
  have hpow : (0:ℝ) < lam μ ^ n := by
    have := lt_trans one_pos (lam_gt_one hμ); positivity
  rw [div_lt_iff₀ hpow]
  rw [div_lt_iff₀ hε] at hn
  linarith

/-- The iterated intertwining relation. -/
theorem itinerary_iterate (μ : ℝ) (x : ℝ) (n : ℕ) :
    itinerary μ ((quadratic μ)^[n] x) = shift^[n] (itinerary μ x) := by
  funext k
  show (if (quadratic μ)^[k] ((quadratic μ)^[n] x) ≤ 1 / 2 then (0 : Fin 2) else 1) = _
  have hs : ∀ (m : ℕ) (t : Sigma2), shift^[m] t = fun j => t (j + m) := by
    intro m
    induction m with
    | zero => intro t; funext j; simp
    | succ m ih =>
      intro t
      funext j
      rw [Function.iterate_succ_apply, ih]
      show t (j + m + 1) = t (j + (m + 1))
      ring_nf
  rw [hs]
  show _ = (if (quadratic μ)^[k + n] x ≤ 1 / 2 then (0 : Fin 2) else 1)
  rw [← Function.iterate_add_apply]


theorem distTerm_eq_of_ne (s t : Sigma2) (i : ℕ) (h : s i ≠ t i) :
    distTerm s t i = 1 / 2 ^ i := by
  have hne := entry_ne s t i h
  have h1 : |s.entry i - t.entry i| = 1 := by
    rcases entry_mem s i with hs | hs <;> rcases entry_mem t i with ht | ht
    · exact absurd (hs.trans ht.symm) hne
    · rw [hs, ht]; norm_num
    · rw [hs, ht]; norm_num
    · exact absurd (hs.trans ht.symm) hne
  rw [distTerm, h1]

/-- The tail of the defining series past index `n` is at most `1 / 2 ^ n`. -/
theorem tail_le (s t : Sigma2) (n : ℕ) :
    ∑' i, distTerm s t (i + (n + 1)) ≤ 1 / 2 ^ n := by
  have hsummable : Summable (fun i => distTerm s t (i + (n + 1))) :=
    (summable_distTerm s t).comp_injective (add_left_injective (n + 1))
  have hg : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + (n + 1))) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).mul_right ((1/2 : ℝ) ^ (n + 1))
  calc ∑' i, distTerm s t (i + (n + 1))
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (n + 1)) :=
        Summable.tsum_le_tsum (fun i => distTerm_le s t _) hsummable hg
    _ = 1 / 2 ^ n := by
        rw [show (fun i : ℕ => (1/2:ℝ) ^ (i + (n+1))) = fun i : ℕ => (1/2:ℝ) ^ (n+1) * (1/2)^i from
          by funext i; rw [pow_add, mul_comm]]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        rw [pow_succ]
        norm_num
        rw [← inv_pow]
        ring

/-- Proposition 6.3. -/
theorem sigma2_dist_agree (s t : Sigma2) (n : ℕ) :
    ((∀ i ≤ n, s i = t i) → dist s t ≤ 1 / 2 ^ n) ∧
      (dist s t < 1 / 2 ^ n → ∀ i ≤ n, s i = t i) := by
  constructor
  · intro h
    have hsplit := (summable_distTerm s t).sum_add_tsum_nat_add (n + 1)
    have hzero : ∑ i ∈ Finset.range (n + 1), distTerm s t i = 0 :=
      Finset.sum_eq_zero fun i hi =>
        distTerm_eq_zero s t i (h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    rw [hzero, zero_add] at hsplit
    rw [dist_eq, ← hsplit]
    exact tail_le s t n
  · intro hlt i hi
    by_contra hne
    have h1 : distTerm s t i = 1 / 2 ^ i := distTerm_eq_of_ne s t i hne
    have h2 : distTerm s t i ≤ ∑' j, distTerm s t j :=
      (summable_distTerm s t).le_tsum i fun j _ => distTerm_nonneg s t j
    have h3 : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ i := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hi
    rw [dist_eq] at hlt
    rw [h1] at h2
    linarith

theorem iterate_shift (n : ℕ) (s : Sigma2) : shift^[n] s = fun k => s (k + n) := by
  induction n generalizing s with
  | zero => funext k; simp
  | succ n ih =>
    funext k
    rw [Function.iterate_succ_apply, ih]
    show s (k + n + 1) = s (k + (n + 1))
    ring_nf

/-- The finite binary word coded by `m`. -/
def wordOf (m : ℕ) : List (Fin 2) := (Encodable.decode (α := List (Fin 2)) m).getD []

/-- The length of the `m`-th block: the word coded by `m`, plus one so no block is empty. -/
def blen (m : ℕ) : ℕ := (wordOf m).length + 1

/-- The position at which the `m`-th block starts. -/
def T (m : ℕ) : ℕ := ∑ j ∈ Finset.range m, blen j

theorem T_succ (m : ℕ) : T (m + 1) = T m + blen m := Finset.sum_range_succ _ _

theorem T_mono : Monotone T := fun i j h =>
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem le_T (m : ℕ) : m ≤ T m := by
  induction m with
  | zero => simp [T]
  | succ k ih =>
    rw [T_succ]
    have h1 : 1 ≤ blen k := Nat.le_add_left 1 _
    omega

theorem blk_ex (p : ℕ) : ∃ m, p < T (m + 1) :=
  ⟨p, lt_of_lt_of_le (Nat.lt_succ_self p) (le_T (p + 1))⟩

/-- The index of the block containing position `p`. -/
def blk (p : ℕ) : ℕ := Nat.find (blk_ex p)

theorem blk_eq {m p : ℕ} (h1 : T m ≤ p) (h2 : p < T (m + 1)) : blk p = m := by
  have hle : blk p ≤ m := Nat.find_le h2
  rcases eq_or_lt_of_le hle with h | h
  · exact h
  · exfalso
    have hs : p < T (blk p + 1) := Nat.find_spec (blk_ex p)
    have hmono : T (blk p + 1) ≤ T m := T_mono (by omega)
    omega

/-- The sequence obtained by writing down every finite binary word in turn. -/
def star : Sigma2 := fun p => (wordOf (blk p)).getD (p - T (blk p)) 0

theorem star_block (m i : ℕ) (hi : i < blen m) :
    star (T m + i) = (wordOf m).getD i 0 := by
  have h2 : T m + i < T (m + 1) := by rw [T_succ]; omega
  have hb : blk (T m + i) = m := blk_eq (Nat.le_add_right _ _) h2
  simp [star, hb]

/-- Proposition 6.6(3). -/
theorem shift_exists_dense_orbit :
    ∃ s : Sigma2, Dense {t : Sigma2 | ∃ n : ℕ, shift^[n] s = t} := by
  refine ⟨star, ?_⟩
  rw [Metric.dense_iff]
  intro t r hr
  obtain ⟨n, hn⟩ := exists_half_pow_lt hr
  set l : List (Fin 2) := List.ofFn (fun i : Fin (n + 1) => t i) with hl
  set m : ℕ := Encodable.encode l with hm
  have hw : wordOf m = l := by simp [wordOf, hm, Encodable.encodek]
  have hll : l.length = n + 1 := by rw [hl]; simp
  refine ⟨shift^[T m] star, ?_, ⟨T m, rfl⟩⟩
  rw [Metric.mem_ball]
  refine lt_of_le_of_lt (dist_le_of_agree _ t n ?_) hn
  intro i hi
  have h1 : (shift^[T m] star) i = star (i + T m) := by rw [iterate_shift]
  have h2 : i < blen m := by rw [blen, hw, hll]; omega
  rw [h1, add_comm, star_block m i h2, hw,
    List.getD_eq_getElem l 0 (by rw [hll]; omega)]
  simp only [hl, List.getElem_ofFn]

/-- The `n`-periodic sequences are exactly the points fixed by `σⁿ`. -/
theorem mem_perOfPeriod_iff (n : ℕ) (s : Sigma2) :
    s ∈ PerOfPeriod (Set.univ : Set Sigma2) shift n ↔ ∀ k, s (k + n) = s k := by
  constructor
  · rintro ⟨-, h⟩ k
    rw [iterate_shift] at h
    exact congrFun h k
  · intro h
    refine ⟨trivial, ?_⟩
    rw [iterate_shift]
    funext k
    exact h k

theorem periodic_mod {n : ℕ} (hn : 0 < n) {s : Sigma2} (hs : ∀ k, s (k + n) = s k) :
    ∀ k, s (k % n) = s k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k n with hk | hk
    · rw [Nat.mod_eq_of_lt hk]
    · have h1 : k % n = (k - n) % n := Nat.mod_eq_sub_mod hk
      have h2 : s (k - n) = s k := by
        have h := hs (k - n)
        rw [Nat.sub_add_cancel hk] at h
        exact h.symm
      rw [h1, ih (k - n) (by omega), h2]

/-- The `n`-periodic sequence generated by a word of length `n`. -/
def periodize {n : ℕ} (hn : 0 < n) (v : Fin n → Fin 2) : Sigma2 :=
  fun k => v ⟨k % n, Nat.mod_lt _ hn⟩

/-- Proposition 6.6(1). -/
theorem shift_ncard_perOfPeriod (n : ℕ) (hn : 0 < n) :
    (PerOfPeriod (Set.univ : Set Sigma2) shift n).ncard = 2 ^ n := by
  have e : (Fin n → Fin 2) ≃ (PerOfPeriod (Set.univ : Set Sigma2) shift n) :=
    { toFun := fun v => ⟨periodize hn v, by
        rw [mem_perOfPeriod_iff]
        intro k
        simp [periodize, Nat.add_mod_right]⟩
      invFun := fun s i => s.1 i
      left_inv := by
        intro v
        funext i
        show periodize hn v i = v i
        simp only [periodize]
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
      right_inv := by
        rintro ⟨s, hs⟩
        rw [mem_perOfPeriod_iff] at hs
        refine Subtype.ext (funext fun k => ?_)
        exact periodic_mod hn hs k }
  have h1 : Nat.card (PerOfPeriod (Set.univ : Set Sigma2) shift n) = 2 ^ n := by
    rw [← Nat.card_congr e]
    simp
  rwa [Nat.card_coe_set_eq] at h1


/-- Differing symbols put the two iterates on opposite sides of the removed gap. -/
theorem gap_of_digit_ne (hμ : 2 + Real.sqrt 5 < μ) {x y : ℝ}
    (hx : x ∈ Lambda μ) (hy : y ∈ Lambda μ) {i : ℕ} (hne : itinerary μ x i ≠ itinerary μ y i) :
    rad μ ≤ |(quadratic μ)^[i] x - (quadratic μ)^[i] y| := by
  have hpx := mem_pieceOf_itinerary hμ hx i
  have hpy := mem_pieceOf_itinerary hμ hy i
  by_cases hb : itinerary μ x i = 0
  · have hb' : itinerary μ y i = 1 := by omega
    rw [hb] at hpx; rw [hb'] at hpy
    have h1 : (quadratic μ)^[i] x ≤ pm μ := (show _ ∈ I0 μ by simpa [pieceOf] using hpx).2
    have h2 : pp μ ≤ (quadratic μ)^[i] y := (show _ ∈ I1 μ by simpa [pieceOf] using hpy).1
    have hkey : rad μ ≤ -((quadratic μ)^[i] x - (quadratic μ)^[i] y) := by
      unfold pm at h1; unfold pp at h2; linarith
    exact le_trans hkey (neg_le_abs _)
  · have hb1 : itinerary μ x i = 1 := by omega
    have hb' : itinerary μ y i = 0 := by omega
    rw [hb1] at hpx; rw [hb'] at hpy
    have h1 : pp μ ≤ (quadratic μ)^[i] x := (show _ ∈ I1 μ by simpa [pieceOf] using hpx).1
    have h2 : (quadratic μ)^[i] y ≤ pm μ := (show _ ∈ I0 μ by simpa [pieceOf] using hpy).2
    have hkey : rad μ ≤ (quadratic μ)^[i] x - (quadratic μ)^[i] y := by
      unfold pp at h1; unfold pm at h2; linarith
    exact le_trans hkey (le_abs_self _)

/-- Every point of `Λ` has a companion agreeing with it to any prescribed depth and differing
immediately after. -/
theorem exists_partner (hμ : 2 + Real.sqrt 5 < μ) {x : ℝ} (hx : x ∈ Lambda μ) (N : ℕ) :
    ∃ y ∈ Lambda μ, (∀ i < N, itinerary μ y i = itinerary μ x i) ∧
      itinerary μ y N ≠ itinerary μ x N := by
  obtain ⟨y, hy, hyt⟩ := itinerary_surjOn hμ
    (fun i => if i = N then (if itinerary μ x N = 0 then 1 else 0) else itinerary μ x i)
  refine ⟨y, hy, ?_, ?_⟩
  · intro i hi
    rw [hyt]
    simp [Nat.ne_of_lt hi]
  · rw [hyt]
    by_cases hb : itinerary μ x N = 0
    · simp [hb]
    · have h1 : itinerary μ x N = 1 := by omega
      simp [h1]

theorem lambdaMap_conjugate_shift (hμ : 2 + Real.sqrt 5 < μ) :
    TopologicallyConjugate (lambdaMap μ) shift := by
  obtain ⟨h, hh⟩ := itinerary_homeomorph hμ
  refine ⟨h, fun x => ?_⟩
  rw [hh, hh]
  show itinerary μ (quadratic μ x.1) = shift (itinerary μ x.1)
  have := itinerary_iterate μ x.1 1
  simpa using this

theorem quadratic_sensitiveDependence (hμ : 2 + Real.sqrt 5 < μ) :
    SensitiveDependence (Lambda μ) (quadratic μ) := by
  have hr := rad_pos hμ
  refine ⟨rad μ / 2, by linarith, ?_⟩
  intro x hx ε hε
  obtain ⟨N, hN⟩ := exists_pow_lam_lt hμ hε
  obtain ⟨y, hy, hagree, hdiff⟩ := exists_partner hμ hx N
  refine ⟨y, hy, ?_, N, ?_⟩
  · have hclose := close_of_agree hμ hx hy N (fun i hi => (hagree i hi).symm)
    rw [Real.dist_eq]
    linarith
  · have hgap := gap_of_digit_ne hμ hx hy (i := N) (fun hc => hdiff hc.symm)
    rw [Real.dist_eq]
    linarith

theorem quadratic_dense_per (hμ : 2 + Real.sqrt 5 < μ) :
    Lambda μ ⊆ closure (Per (Lambda μ) (quadratic μ)) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lam_lt hμ hε
  set p : Sigma2 := periodize (Nat.succ_pos N) (fun i : Fin (N + 1) => itinerary μ x i) with hp
  obtain ⟨y, hy, hyp⟩ := itinerary_surjOn hμ p
  have hper : shift^[N + 1] p = p := by
    rw [iterate_shift]
    funext k
    simp [hp, periodize, Nat.add_mod_right]
  have hfix : (quadratic μ)^[N + 1] y = y := by
    refine itinerary_injOn hμ (lambda_iterate hy (N + 1)) hy ?_
    rw [itinerary_iterate, hyp, hper]
  refine ⟨y, ⟨hy, N + 1, Nat.succ_pos N, hfix⟩, ?_⟩
  have hagree : ∀ i < N, itinerary μ x i = itinerary μ y i := by
    intro i hi
    rw [hyp, hp]
    show _ = (fun j : Fin (N + 1) => itinerary μ x j) ⟨i % (N + 1), _⟩
    congr 1
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hclose := close_of_agree hμ hx hy N hagree
  rw [Real.dist_eq]
  linarith


theorem lambda_isCantorSet (hμ : 2 + Real.sqrt 5 < μ) : IsCantorSet (Lambda μ) := by
  have hhalf1 := pm_lt_half hμ
  have hhalf2 := half_lt_pp hμ
  refine ⟨fun x hx => hx 0, lambda_isClosed, ?_, ?_⟩
  · intro a b hab hsub
    have ha : a ∈ Lambda μ := hsub (Set.left_mem_Icc.2 (le_of_lt hab))
    have hb : b ∈ Lambda μ := hsub (Set.right_mem_Icc.2 (le_of_lt hab))
    have hsame : itinerary μ a = itinerary μ b := by
      funext n
      by_contra hne
      have hpa := mem_pieceOf_itinerary hμ ha n
      have hpb := mem_pieceOf_itinerary hμ hb n
      have hmid : (1/2 : ℝ) ∈ Set.uIcc ((quadratic μ)^[n] a) ((quadratic μ)^[n] b) := by
        rw [Set.mem_uIcc]
        by_cases hb0 : itinerary μ a n = 0
        · have hb1 : itinerary μ b n = 1 := by omega
          rw [hb0] at hpa; rw [hb1] at hpb
          have h1 : (quadratic μ)^[n] a ≤ pm μ := (show _ ∈ I0 μ by simpa [pieceOf] using hpa).2
          have h2 : pp μ ≤ (quadratic μ)^[n] b := (show _ ∈ I1 μ by simpa [pieceOf] using hpb).1
          exact Or.inl ⟨by linarith, by linarith⟩
        · have ha1 : itinerary μ a n = 1 := by omega
          have hb1 : itinerary μ b n = 0 := by omega
          rw [ha1] at hpa; rw [hb1] at hpb
          have h1 : pp μ ≤ (quadratic μ)^[n] a := (show _ ∈ I1 μ by simpa [pieceOf] using hpa).1
          have h2 : (quadratic μ)^[n] b ≤ pm μ := (show _ ∈ I0 μ by simpa [pieceOf] using hpb).2
          exact Or.inr ⟨by linarith, by linarith⟩
      have hcont : ContinuousOn ((quadratic μ)^[n]) (Set.uIcc a b) :=
        (continuous_quadratic.iterate n).continuousOn
      obtain ⟨z, hz, hzv⟩ := intermediate_value_uIcc hcont hmid
      have hzab : z ∈ Set.Icc a b := by
        rwa [Set.uIcc_of_le (le_of_lt hab)] at hz
      have hzL : z ∈ Lambda μ := hsub hzab
      have := lambda_subset_pieces hμ (lambda_iterate hzL n)
      rcases this with h0 | h1
      · have : (quadratic μ)^[n] z ≤ pm μ := h0.2
        rw [hzv] at this; linarith
      · have : pp μ ≤ (quadratic μ)^[n] z := h1.1
        rw [hzv] at this; linarith
    exact absurd (itinerary_injOn hμ ha hb hsame) (ne_of_lt hab)
  · intro x hx
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨N, hN⟩ := exists_pow_lam_lt hμ hε
    obtain ⟨y, hy, hagree, hdiff⟩ := exists_partner hμ hx N
    have hclose := close_of_agree hμ hx hy N (fun i hi => (hagree i hi).symm)
    refine ⟨y, ⟨hball ?_, hy⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
      linarith
    · intro hyx
      rw [hyx] at hdiff
      exact hdiff rfl

theorem quadratic_exists_dense_orbit (hμ : 2 + Real.sqrt 5 < μ) :
    ∃ x ∈ Lambda μ, Lambda μ ⊆ closure {y : ℝ | ∃ n : ℕ, (quadratic μ)^[n] x = y} := by
  obtain ⟨s, hs⟩ := shift_exists_dense_orbit
  obtain ⟨x, hx, hxs⟩ := itinerary_surjOn hμ s
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lam_lt hμ hε
  have hpos : (0:ℝ) < 1 / 2 ^ N := by positivity
  rw [Metric.dense_iff] at hs
  obtain ⟨t, htb, n, htn⟩ := hs (itinerary μ y) (1 / 2 ^ N) hpos
  rw [Metric.mem_ball] at htb
  have hagree : ∀ i ≤ N, t i = itinerary μ y i := by
    have := (sigma2_dist_agree t (itinerary μ y) N).2
    exact this htb
  refine ⟨(quadratic μ)^[n] x, ⟨n, rfl⟩, ?_⟩
  have hit : itinerary μ ((quadratic μ)^[n] x) = t := by
    rw [itinerary_iterate, hxs, htn]
  have hmem := lambda_iterate hx n
  have hclose := close_of_agree hμ hy hmem N ?_
  · rw [Real.dist_eq]
    linarith
  · intro i hi
    rw [hit]
    exact (hagree i (by omega)).symm


/-- The itinerary map carries the period-`n` points of `Fμ` on `Λ` bijectively onto those of
the shift. -/
theorem image_perOfPeriod (hμ : 2 + Real.sqrt 5 < μ) (n : ℕ) :
    itinerary μ '' (PerOfPeriod (Lambda μ) (quadratic μ) n)
      = PerOfPeriod (Set.univ : Set Sigma2) shift n := by
  ext s
  constructor
  · rintro ⟨x, ⟨hxL, hxfix⟩, rfl⟩
    refine ⟨trivial, ?_⟩
    rw [← itinerary_iterate, hxfix]
  · rintro ⟨-, hs⟩
    obtain ⟨x, hxL, hxs⟩ := itinerary_surjOn hμ s
    refine ⟨x, ⟨hxL, ?_⟩, hxs⟩
    refine itinerary_injOn hμ (lambda_iterate hxL n) hxL ?_
    rw [itinerary_iterate, hxs, hs]

theorem quadratic_ncard_perOfPeriod (hμ : 2 + Real.sqrt 5 < μ) (n : ℕ) (hn : 0 < n) :
    (PerOfPeriod (Lambda μ) (quadratic μ) n).ncard = 2 ^ n := by
  have hinj : Set.InjOn (itinerary μ) (PerOfPeriod (Lambda μ) (quadratic μ) n) :=
    fun a ha b hb h => itinerary_injOn hμ ha.1 hb.1 h
  have := Set.ncard_image_of_injOn hinj
  rw [image_perOfPeriod hμ n] at this
  rw [← this, shift_ncard_perOfPeriod n hn]

end Dev72

open Devaney Devaney.Sigma2 in
theorem solution (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    Lambda μ ⊆ closure (Per (Lambda μ) (quadratic μ)) :=
  Dev72.quadratic_dense_per hμ
