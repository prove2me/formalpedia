-- Prove2me | solution 1 for CloudMWU.Bicriteria.claim_3_2_block_work
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:18:36.682984+00:00
-- url     : https://prove2.me/submissions/9e2b8c2d-8665-481b-8ce0-8337290af31a

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model
import Theorems.Thm_CloudMWU_Bicriteria_lemma_1
import Theorems.Thm_CloudMWU_Bicriteria_lemma_1_quantitative

open Finset CloudMWU.Bicriteria

theorem cmw_bw_queue_nonneg (a ℓ : ℕ → ℝ) (u : ℕ) : 0 ≤ queue a ℓ u := by
  cases u with
  | zero => simp [queue]
  | succ u => simp only [queue]; exact le_max_left _ _

/-- numeric core of the block estimate -/
theorem cmw_bw_num (ε η k E εc ℓ B Ea : ℝ) (m : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hk : 3 / 4 * η ≤ k) (hεc0 : 0 ≤ εc) (hεc : εc ≤ ε ^ 2 * η / 8)
    (hℓ : ℓ ≤ εc * m) (hEa : Ea - 1 ≤ εc) (hE : E ≤ 151 / 100 * ε) (hm : 4 ≤ m)
    (hB0 : 0 ≤ B) (hB : k * B ≤ ℓ + (m + 1) * (Ea - 1) + (m + 1) * (k * E)) :
    (2 + 2 / 100) * B ≤ 4 * ε * m := by
  have hkpos : 0 < k := by nlinarith
  have h1 : k * B ≤ (m + 1) * (2 * εc) + (m + 1) * (k * E) := by nlinarith
  have h2 : 2 * εc ≤ k * (ε / 30) := by nlinarith
  have h3 : k * B ≤ k * ((m + 1) * (ε / 30 + E)) := by nlinarith
  have h4 : B ≤ (m + 1) * (ε / 30 + E) := le_of_mul_le_mul_left h3 hkpos
  nlinarith

set_option maxHeartbeats 2000000 in
theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h)
    (r m : ℕ) (hm : sTilde N ε η ≤ (m : ℝ))
    (i₀ : Fin N) (hbusy : ∀ τ ∈ Icc r (r + m), 0 < runQueue h L τ i₀) :
    (1 - 4 * ε) * (m : ℝ)
      ≤ ∑ τ ∈ Ico r (r + m), ∑ i, work (fun s => h s i) (fun s => L s i) τ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hεN : 0 < ε / (N : ℝ) := by positivity
  have hsimp : ∀ τ, h τ ∈ truncSimplex N ε := by
    intro τ
    cases τ with
    | zero => exact hrun.1
    | succ τ => exact (hrun.2 τ).2.1
  have hpos : ∀ τ i, 0 ≤ h τ i := fun τ i => le_trans hεN.le ((hsimp τ).2 i)
  have hle1 : ∀ τ i, h τ i ≤ 1 := by
    intro τ i
    have := Finset.single_le_sum (f := h τ) (fun j _ => hpos τ j) (Finset.mem_univ i)
    rw [(hsimp τ).1] at this; exact this
  -- constants
  set c := cLem1 N ε η with hc_def
  have hc : c = ε * η / (4 * (N : ℝ)) := rfl
  have hc0 : 0 < c := by rw [hc]; positivity
  have hεc : ε * c ≤ ε ^ 2 * η / 8 := by
    rw [hc, show ε * (ε * η / (4 * (N : ℝ))) = ε ^ 2 * η / (4 * (N : ℝ)) by ring]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hεc1 : ε * c ≤ 1 / 100 := by
    have : ε ^ 2 * η / 8 ≤ 1 / 100 := by
      have : ε ^ 2 ≤ 1 / 100 := by nlinarith
      nlinarith
    linarith
  set Ea := Real.exp (lam N ε * η) with hEa
  set Em := Real.exp (-η) with hEm
  set E := Real.exp (η * (1 + lam N ε)) * ε with hE
  set k := Ea - Em with hk
  have hlam : lam N ε = ε ^ 2 / (8 * (N : ℝ)) := rfl
  have hlamη : lam N ε * η = ε * c / 2 := by rw [hlam, hc]; field_simp; ring
  have hlam0 : 0 ≤ lam N ε * η := by rw [hlamη]; positivity
  have hEa1 : 1 ≤ Ea := Real.one_le_exp hlam0
  have hEa2 : Ea - 1 ≤ ε * c := by
    have h1 : 1 - lam N ε * η ≤ Real.exp (-(lam N ε * η)) := by
      linarith [Real.add_one_le_exp (-(lam N ε * η))]
    have h2 : Ea * Real.exp (-(lam N ε * η)) = 1 := by rw [hEa, ← Real.exp_add]; simp
    have hx : lam N ε * η ≤ 1 / 200 := by rw [hlamη]; linarith
    nlinarith
  have hk3 : 3 / 4 * η ≤ k := by
    have hEm1 : Em * Real.exp η = 1 := by rw [hEm, ← Real.exp_add]; simp
    have he := Real.add_one_le_exp η
    have hEm0 : 0 < Em := Real.exp_pos _
    have h1 : Em * (1 + η) ≤ 1 := by nlinarith
    have h2 : 3 / 4 * η ≤ 1 - Em := by nlinarith
    rw [hk]; linarith
  have hEbound : E ≤ 151 / 100 * ε := by
    have hlam1 : lam N ε ≤ 1 / 1600 := by
      rw [hlam, div_le_iff₀ (by positivity)]; nlinarith
    have hlampos : 0 ≤ lam N ε := by rw [hlam]; positivity
    set x := η * (1 + lam N ε) with hx
    have hx1 : x ≤ 3337 / 10000 := by
      rw [hx]; nlinarith
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos x
    have h3 : Real.exp x ≤ 151 / 100 := by nlinarith
    rw [hE]; nlinarith
  -- inactive mass
  set b : ℕ → ℝ := fun τ => ∑ j ∈ (active h L τ)ᶜ, h τ j with hb
  have hb0 : ∀ τ, 0 ≤ b τ := fun τ => Finset.sum_nonneg (fun j _ => hpos τ j)
  set Z : ℕ → ℝ := fun τ => Ea - k * (b τ - E) with hZ
  -- Step A: growth of the busy user
  have hA : ∀ τ ∈ Icc r (r + m), h τ i₀ ≤ h (τ + 1) i₀ * Z τ := by
    intro τ hτ
    have hi : i₀ ∈ active h L τ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbusy τ hτ⟩
    exact lemma_1_quantitative N hN ε η hε hε' hη hη' β L hL h hrun τ i₀ hi
  -- Step B: iterate
  have hB : ∀ n, n ≤ m + 1 →
      h r i₀ ≤ h (r + n) i₀ * Real.exp (∑ j ∈ range n, (Z (r + j) - 1)) := by
    intro n
    induction n with
    | zero => intro _; simp only [add_zero, Finset.range_zero, Finset.sum_empty, Real.exp_zero, mul_one]; exact le_rfl
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hstep := hA (r + n) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hZe : Z (r + n) ≤ Real.exp (Z (r + n) - 1) := by
        linarith [Real.add_one_le_exp (Z (r + n) - 1)]
      have h1 : h (r + n) i₀ ≤ h (r + n + 1) i₀ * Real.exp (Z (r + n) - 1) :=
        le_trans hstep (mul_le_mul_of_nonneg_left hZe (hpos _ _))
      rw [Finset.sum_range_succ, Real.exp_add]
      have e : r + (n + 1) = r + n + 1 := by omega
      rw [e]
      calc h r i₀ ≤ h (r + n) i₀ * Real.exp (∑ j ∈ range n, (Z (r + j) - 1)) := ih'
        _ ≤ (h (r + n + 1) i₀ * Real.exp (Z (r + n) - 1))
              * Real.exp (∑ j ∈ range n, (Z (r + j) - 1)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = h (r + n + 1) i₀ * (Real.exp (∑ j ∈ range n, (Z (r + j) - 1))
              * Real.exp (Z (r + n) - 1)) := by ring
  -- Step C: total inactive mass over the block
  set Bt := ∑ j ∈ range (m + 1), b (r + j) with hBt
  have hC : k * Bt ≤ Real.log ((N : ℝ) / ε) + ((m : ℝ) + 1) * (Ea - 1)
      + ((m : ℝ) + 1) * (k * E) := by
    have h1 := hB (m + 1) le_rfl
    have h2 : h (r + (m + 1)) i₀ * Real.exp (∑ j ∈ range (m + 1), (Z (r + j) - 1))
        ≤ Real.exp (∑ j ∈ range (m + 1), (Z (r + j) - 1)) := by
      have := hle1 (r + (m + 1)) i₀
      have := Real.exp_pos (∑ j ∈ range (m + 1), (Z (r + j) - 1))
      nlinarith
    have h3 : ε / (N : ℝ) ≤ Real.exp (∑ j ∈ range (m + 1), (Z (r + j) - 1)) :=
      le_trans ((hsimp r).2 i₀) (le_trans h1 h2)
    have h4 : Real.log (ε / (N : ℝ)) ≤ ∑ j ∈ range (m + 1), (Z (r + j) - 1) := by
      rw [← Real.log_exp (∑ j ∈ range (m + 1), (Z (r + j) - 1))]
      exact Real.log_le_log hεN h3
    have h5 : Real.log (ε / (N : ℝ)) = - Real.log ((N : ℝ) / ε) := by
      rw [← Real.log_inv, inv_div]
    have h6 : ∑ j ∈ range (m + 1), (Z (r + j) - 1)
        = ((m : ℝ) + 1) * (Ea - 1) + ((m : ℝ) + 1) * (k * E) - k * Bt := by
      have e1 : ∑ j ∈ range (m + 1), (Z (r + j) - 1)
          = ∑ j ∈ range (m + 1), (((Ea - 1) + k * E) - k * b (r + j)) :=
        Finset.sum_congr rfl (fun j _ => by simp only [hZ]; ring)
      rw [e1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, hBt]
      push_cast
      ring
    linarith
  -- Step D: per-step work
  have hD : ∀ τ, 1 - b τ - (102 / 100) * b (τ + 1)
      ≤ ∑ i, work (fun s => h s i) (fun s => L s i) τ := by
    intro τ
    set A := active h L τ with hAdef
    set A' := active h L (τ + 1) with hA'def
    have hw0 : ∀ i, 0 ≤ work (fun s => h s i) (fun s => L s i) τ := fun i =>
      le_min (hpos τ i) (add_nonneg (hL τ i) (cmw_bw_queue_nonneg _ _ _))
    -- work on A ∩ A' equals allocation
    have hwA : ∀ j ∈ A, j ∈ A' → work (fun s => h s j) (fun s => L s j) τ = h τ j := by
      intro j _ hj'
      have hq : 0 < runQueue h L (τ + 1) j := (Finset.mem_filter.mp hj').2
      unfold runQueue at hq
      simp only [queue] at hq
      have : 0 < L τ j + queue (fun s => h s j) (fun s => L s j) τ - h τ j := by
        by_contra hcon; push_neg at hcon
        rw [max_eq_left hcon] at hq; exact lt_irrefl _ hq
      unfold work; exact min_eq_left (by linarith)
    have hsumA : ∑ j ∈ A, h τ j = 1 - b τ := by
      have := Finset.sum_add_sum_compl A (h τ)
      rw [(hsimp τ).1] at this
      simp only [hb]; linarith
    set X := ∑ j ∈ A.filter (fun j => j ∉ A'), h τ j with hX
    have hX0 : 0 ≤ X := Finset.sum_nonneg (fun j _ => hpos τ j)
    have hwork : ∑ j ∈ A, h τ j - X ≤ ∑ i, work (fun s => h s i) (fun s => L s i) τ := by
      have h1 : ∑ j ∈ A, h τ j = ∑ j ∈ A.filter (fun j => j ∈ A'), h τ j + X :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have h2 : ∑ j ∈ A.filter (fun j => j ∈ A'), h τ j
          = ∑ j ∈ A.filter (fun j => j ∈ A'), work (fun s => h s j) (fun s => L s j) τ :=
        Finset.sum_congr rfl (fun j hj => by
          have := Finset.mem_filter.mp hj
          rw [hwA j this.1 this.2])
      have h3 : ∑ j ∈ A.filter (fun j => j ∈ A'), work (fun s => h s j) (fun s => L s j) τ
          ≤ ∑ i, work (fun s => h s i) (fun s => L s i) τ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw0 i)
      linarith
    -- X is controlled by the next inactive mass
    have hl1 := (lemma_1 N hN ε η hε hε' hη hη' β L hL h hrun τ).2
    have hXb : (1 - ε * c) * X ≤ b (τ + 1) := by
      rw [hX, Finset.mul_sum]
      calc ∑ j ∈ A.filter (fun j => j ∉ A'), (1 - ε * c) * h τ j
          ≤ ∑ j ∈ A.filter (fun j => j ∉ A'), h (τ + 1) j := by
            apply Finset.sum_le_sum
            intro j hj
            have hjA := (Finset.mem_filter.mp hj).1
            by_cases hjb : h τ j < β j
            · have := hl1.1 j hjA hjb
              have := hpos τ j
              nlinarith
            · push_neg at hjb
              have := hl1.2 j hjA hjb
              linarith
        _ ≤ b (τ + 1) := by
            simp only [hb]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              rw [Finset.mem_compl]
              exact (Finset.mem_filter.mp hj).2
            · intro j _ _; exact hpos _ _
    have hX2 : X ≤ (102 / 100) * b (τ + 1) := by
      have : 99 / 100 * X ≤ (1 - ε * c) * X := by
        apply mul_le_mul_of_nonneg_right (by linarith) hX0
      linarith
    linarith
  -- Step E: sum over the block
  have hE' : (m : ℝ) - (2 + 2 / 100) * Bt
      ≤ ∑ τ ∈ Ico r (r + m), ∑ i, work (fun s => h s i) (fun s => L s i) τ := by
    have hshift : ∑ τ ∈ Ico r (r + m), ∑ i, work (fun s => h s i) (fun s => L s i) τ
        = ∑ j ∈ range m, ∑ i, work (fun s => h s i) (fun s => L s i) (r + j) := by
      rw [Finset.sum_Ico_eq_sum_range]; simp
    rw [hshift]
    have h1 : ∑ j ∈ range m, (1 - b (r + j) - (102 / 100) * b (r + j + 1))
        ≤ ∑ j ∈ range m, ∑ i, work (fun s => h s i) (fun s => L s i) (r + j) :=
      Finset.sum_le_sum (fun j _ => hD (r + j))
    have h2 : ∑ j ∈ range m, b (r + j) ≤ Bt := by
      rw [hBt, Finset.sum_range_succ]; linarith [hb0 (r + m)]
    have h3 : ∑ j ∈ range m, b (r + j + 1) ≤ Bt := by
      rw [hBt, Finset.sum_range_succ']
      have : ∑ j ∈ range m, b (r + j + 1) = ∑ j ∈ range m, b (r + (j + 1)) :=
        Finset.sum_congr rfl (fun j _ => by rw [add_assoc])
      rw [this]; simp only [add_zero]; linarith [hb0 r]
    have h4 : ∑ j ∈ range m, (1 - b (r + j) - (102 / 100) * b (r + j + 1))
        = (m : ℝ) - ∑ j ∈ range m, b (r + j) - (102 / 100) * ∑ j ∈ range m, b (r + j + 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, Finset.mul_sum]
    linarith
  -- Step F: numerics
  have hlogpos : 0 < Real.log ((N : ℝ) / ε) := by
    apply Real.log_pos
    rw [one_lt_div hε]; linarith
  have hst : sTilde N ε η = Real.log ((N : ℝ) / ε) / (ε * c) := rfl
  have hℓ : Real.log ((N : ℝ) / ε) ≤ ε * c * (m : ℝ) := by
    rw [hst, div_le_iff₀ (by positivity)] at hm; linarith
  have hm4 : (4 : ℝ) ≤ m := by
    have hlog1 : 1 ≤ Real.log ((N : ℝ) / ε) := by
      have h20 : (20 : ℝ) ≤ (N : ℝ) / ε := by
        rw [le_div_iff₀ hε]; nlinarith
      have he : Real.exp 1 ≤ (N : ℝ) / ε := by
        have := Real.exp_one_lt_d9; linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 1) he
    have : (4 : ℝ) ≤ sTilde N ε η := by
      rw [hst, le_div_iff₀ (by positivity)]; linarith
    linarith
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg (fun j _ => hb0 _)
  have hnum := cmw_bw_num ε η k E (ε * c) (Real.log ((N : ℝ) / ε)) Bt Ea (m : ℝ) hε hε' hη hk3
    (by positivity) hεc hℓ hEa2 hEbound hm4 hBt0 hC
  linarith
