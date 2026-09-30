-- Prove2me | solution 1 for DrezetGHZ.appendix_superdeterministic_model_reproduces_ghz
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:28:35.529648+00:00
-- url     : https://prove2.me/submissions/0bb79e07-a279-44ba-a6f9-b46b04a5bd9a

import Definitions.Def_DrezetGHZ_Models
set_option autoImplicit false
open DrezetGHZ Matrix MeasureTheory

set_option maxHeartbeats 800000 in
private theorem born_cases (α β γ : ℤˣ) :
    bornProb .x .x .x α β γ = (if α * β * γ = -1 then 1 / 4 else 0) ∧
    bornProb .x .y .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .x .y α β γ = (if α * β * γ = 1 then 1 / 4 else 0) ∧
    bornProb .y .y .x α β γ = (if α * β * γ = 1 then 1 / 4 else 0) := by
  have hs2r : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast hs2r
  have hs4 : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  rcases Int.units_eq_one_or α with rfl | rfl <;>
    rcases Int.units_eq_one_or β with rfl | rfl <;>
    rcases Int.units_eq_one_or γ with rfl | rfl <;>
    norm_num [bornProb, productKet, spinEigenvector, dotProduct, ghzState,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.sq_sqrt] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.normSq_mul, hs4,
      Complex.normSq_ofReal, Real.sq_sqrt]

set_option maxHeartbeats 1600000 in
theorem solution (n₁ n₂ n₃ : Setting)
    (hn : (n₁, n₂, n₃) ∈ ({(.x, .x, .x), (.x, .y, .y), (.y, .x, .y), (.y, .y, .x)} :
      Finset (Setting × Setting × Setting)))
    (α β γ : ℤˣ) :
    ∫ θ, appendixResponse θ.1 n₁ α * appendixResponse θ.2.1 n₂ β *
        appendixResponse θ.2.2 n₃ γ ∂(appendixDensity n₁ n₂ n₃) =
      bornProb n₁ n₂ n₃ α β γ := by
  have hu : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext u
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  have hb := born_cases α β γ
  unfold appendixDensity
  rw [integral_smul_measure, integral_finsetSum_measure (fun v _ => integrable_dirac (by exact enorm_lt_top))]
  simp only [integral_dirac, Finset.sum_filter, Fintype.sum_prod_type]
  cases n₁ <;> cases n₂ <;> cases n₃ <;>
    rcases Int.units_eq_one_or α with rfl | rfl <;>
    rcases Int.units_eq_one_or β with rfl | rfl <;>
    rcases Int.units_eq_one_or γ with rfl | rfl <;>
    norm_num [Finset.univ_product_univ, hu, Finset.sum_filter,
      appendixResponse, settingAngle, ghzSign] at hn hb ⊢ <;> tauto
