-- Prove2me | solution 1 for CVPricing.CertEquiv.case_t_two
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:03:49.377831+00:00
-- url     : https://prove2.me/submissions/4e68e97a-7d28-4871-8c89-15b961502dda

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_CEPrice

set_option autoImplicit false
open KeskinZeevi.SufficientConditions CVPricing.CertEquiv Matrix

theorem ls2 (p D : ℕ → ℝ) (h : p 1 ≠ p 2) :
    lsEstimateOf p D 2 = ((D 1 * p 2 - D 2 * p 1) / (p 2 - p 1), (D 2 - D 1) / (p 2 - p 1)) := by
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hne : p 2 - p 1 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have hJ : fisherOf p 2 = !![(2 : ℝ), p 1 + p 2; p 1 + p 2, p 1 ^ 2 + p 2 ^ 2] := by
    unfold fisherOf
    rw [hI, Finset.sum_pair (by norm_num)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hdet : (fisherOf p 2).det = (p 2 - p 1) ^ 2 := by
    rw [hJ, Matrix.det_fin_two_of]; ring
  have hdetU : IsUnit (fisherOf p 2).det := by
    rw [hdet]; exact IsUnit.mk0 _ (pow_ne_zero 2 hne)
  unfold lsEstimateOf
  simp only
  rw [hI, Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)]
  set w : Fin 2 → ℝ := ![(D 1 * p 2 - D 2 * p 1) / (p 2 - p 1), (D 2 - D 1) / (p 2 - p 1)] with hw
  have hJw : (fisherOf p 2) *ᵥ w = ![D 1 + D 2, D 1 * p 1 + D 2 * p 2] := by
    rw [hJ]
    ext i
    fin_cases i
    · simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring
    · simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring
  have : (fisherOf p 2)⁻¹ *ᵥ ![D 1 + D 2, D 1 * p 1 + D 2 * p 2] = w := by
    rw [← hJw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mulVec]
  rw [this]
  simp [hw]

theorem lsEstimateOf_congr (p p' D D' : ℕ → ℝ) (t : ℕ) (hp : ∀ s ∈ Finset.Icc 1 t, p s = p' s)
    (hD : ∀ s ∈ Finset.Icc 1 t, D s = D' s) : lsEstimateOf p D t = lsEstimateOf p' D' t := by
  unfold lsEstimateOf fisherOf
  have h1 : ∑ s ∈ Finset.Icc 1 t, !![(1 : ℝ), p s; p s, p s ^ 2] =
      ∑ s ∈ Finset.Icc 1 t, !![(1 : ℝ), p' s; p' s, p' s ^ 2] :=
    Finset.sum_congr rfl fun s hs => by rw [hp s hs]
  have h2 : ∑ s ∈ Finset.Icc 1 t, D s = ∑ s ∈ Finset.Icc 1 t, D' s :=
    Finset.sum_congr rfl hD
  have h3 : ∑ s ∈ Finset.Icc 1 t, D s * p s = ∑ s ∈ Finset.Icc 1 t, D' s * p' s :=
    Finset.sum_congr rfl fun s hs => by rw [hD s hs, hp s hs]
  rw [h1, h2, h3]

theorem solution (M : CVPricing.CertEquiv.Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (h12 : p₁ < p₂) (e : ℕ → ℝ) :
    lsEstimateOf (cePrice M p₁ p₂ e) (demandOf M (cePrice M p₁ p₂ e) e) 2 =
        (M.a₀ + (e 1 * p₂ - e 2 * p₁) / (p₂ - p₁), M.a₁ + (e 2 - e 1) / (p₂ - p₁)) ∧
      (-M.a₁ * (p₂ - p₁) * (2 * M.ph) ≤ (p₂ - 2 * M.ph) * e 1 + (2 * M.ph - p₁) * e 2 →
        cePrice M p₁ p₂ e 3 = M.ph) := by
  have hc1 : cePrice M p₁ p₂ e 1 = p₁ := by rw [cePrice]; simp
  have hc2 : cePrice M p₁ p₂ e 2 = p₂ := by rw [cePrice]; simp
  have hne : p₂ - p₁ ≠ 0 := (sub_pos.2 h12).ne'
  have hest : lsEstimateOf (cePrice M p₁ p₂ e) (demandOf M (cePrice M p₁ p₂ e) e) 2 =
      (M.a₀ + (e 1 * p₂ - e 2 * p₁) / (p₂ - p₁), M.a₁ + (e 2 - e 1) / (p₂ - p₁)) := by
    rw [ls2 _ _ (by rw [hc1, hc2]; exact h12.ne)]
    simp only [demandOf, hc1, hc2]
    ext
    · field_simp; ring
    · field_simp; ring
  refine ⟨hest, fun hcond => ?_⟩
  have h3 : cePrice M p₁ p₂ e 3 = ceRule M (lsEstimateOf
      (fun s => if s < 3 then cePrice M p₁ p₂ e s else 0)
      (fun s => if s < 3 then M.a₀ + M.a₁ * cePrice M p₁ p₂ e s + e s else 0) (3 - 1)) := by
    rw [cePrice]; simp
  rw [h3]
  have hcongr : lsEstimateOf (fun s => if s < 3 then cePrice M p₁ p₂ e s else 0)
      (fun s => if s < 3 then M.a₀ + M.a₁ * cePrice M p₁ p₂ e s + e s else 0) (3 - 1) =
      lsEstimateOf (cePrice M p₁ p₂ e) (demandOf M (cePrice M p₁ p₂ e) e) 2 := by
    apply lsEstimateOf_congr
    · intro s hs
      rw [Finset.mem_Icc] at hs
      simp only [show s < 3 by omega, if_true]
    · intro s hs
      rw [Finset.mem_Icc] at hs
      simp only [show s < 3 by omega, if_true, demandOf]
  rw [hcongr, hest]
  unfold ceRule
  simp only
  set a1 : ℝ := M.a₁ + (e 2 - e 1) / (p₂ - p₁) with ha1
  set a0 : ℝ := M.a₀ + (e 1 * p₂ - e 2 * p₁) / (p₂ - p₁) with ha0
  by_cases h0 : 0 ≤ a1
  · simp [h0]
  · rw [if_neg h0]
    push_neg at h0
    have hkey : 0 ≤ a0 + 2 * M.ph * a1 := by
      have hpos : 0 < p₂ - p₁ := sub_pos.2 h12
      have : a0 + 2 * M.ph * a1 = M.a₀ + 2 * M.ph * M.a₁ +
          ((p₂ - 2 * M.ph) * e 1 + (2 * M.ph - p₁) * e 2) / (p₂ - p₁) := by
        rw [ha0, ha1]; field_simp; ring
      rw [this]
      have h2 : -(2 * M.ph * M.a₁) ≤ ((p₂ - 2 * M.ph) * e 1 + (2 * M.ph - p₁) * e 2) / (p₂ - p₁) := by
        rw [le_div_iff₀ hpos]; nlinarith
      have := M.a₀_pos
      linarith
    have hge : M.ph ≤ -a0 / (2 * a1) := by
      rw [le_div_iff_of_neg (by linarith)]
      linarith
    have : min M.ph (-a0 / (2 * a1)) = M.ph := min_eq_left hge
    rw [this]
    exact max_eq_right M.pl_lt_ph.le
