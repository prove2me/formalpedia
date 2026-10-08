-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:21:06.407898+00:00
-- url     : https://prove2.me/submissions/50dc38b4-1512-409b-9231-90e3b880df11

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

open Matrix

namespace P6ebbe7d6

open Matrix in
lemma key {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.PosDef) (b : Fin d → ℝ) :
    D *ᵥ (D⁻¹ *ᵥ b) = b ∧ (D⁻¹ *ᵥ b) ᵥ* D = b := by
  have hu := hD.isUnit
  have h1 : D *ᵥ (D⁻¹ *ᵥ b) = b := by
    rw [mulVec_mulVec, mul_nonsing_inv D ((isUnit_iff_isUnit_det D).mp hu), one_mulVec]
  refine ⟨h1, ?_⟩
  have hT : Dᵀ = D := by
    have h := hD.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (D⁻¹ *ᵥ b) ᵥ* Dᵀ = D *ᵥ (D⁻¹ *ᵥ b) := vecMul_transpose _ _
  rw [hT] at h2
  rw [h2, h1]

open Matrix in
lemma quad {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.PosDef) (b z : Fin d → ℝ) (t : ℝ) :
    2 * t * (b ⬝ᵥ z) - t ^ 2 * (b ⬝ᵥ (D⁻¹ *ᵥ b)) ≤ z ⬝ᵥ (D *ᵥ z) := by
  obtain ⟨h1, h2⟩ := key D hD b
  set w := D⁻¹ *ᵥ b with hw
  have h0 := hD.posSemidef.dotProduct_mulVec_nonneg (z - t • w)
  have hs : star (z - t • w) = z - t • w := by
    ext i; simp
  rw [hs] at h0
  have e1 : w ⬝ᵥ (D *ᵥ z) = b ⬝ᵥ z := by rw [dotProduct_mulVec, h2]
  have e2 : z ⬝ᵥ (D *ᵥ w) = b ⬝ᵥ z := by rw [h1, dotProduct_comm]
  have e3 : w ⬝ᵥ (D *ᵥ w) = b ⬝ᵥ w := by rw [h1, dotProduct_comm]
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, e1, e2, e3] at h0
  nlinarith [h0]

lemma dot_pos {d : ℕ} (hd : 0 < d) (u v : Fin d → ℝ) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) :
    0 < u ⬝ᵥ v := by
  unfold dotProduct
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact Finset.sum_pos (fun i _ => mul_pos (hu i) (hv i)) Finset.univ_nonempty

end P6ebbe7d6

open Matrix in
theorem solution {d : ℕ} (hd : 0 < d) (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (b : Fin d → ℝ) (hb : ∀ i, 0 < b i)
    (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.PosDef)
    (hDb : ∀ i, 0 < (D⁻¹ *ᵥ b) i) :
    (∀ z : Fin d → ℝ, (∀ i, 0 < z i) →
        Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b))))
          ≤ (c + 1 / (2 * σ) * (z ⬝ᵥ (D *ᵥ z))) / (b ⬝ᵥ z)) ∧
    (∀ i, 0 < (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)) i) ∧
    (c + 1 / (2 * σ) * ((Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b))
          ⬝ᵥ (D *ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)))))
        / (b ⬝ᵥ (Real.sqrt (2 * c * σ / (b ⬝ᵥ (D⁻¹ *ᵥ b))) • (D⁻¹ *ᵥ b)))
      = Real.sqrt (2 * c / (σ * (b ⬝ᵥ (D⁻¹ *ᵥ b)))) := by
  obtain ⟨h1, h2⟩ := P6ebbe7d6.key D hD b
  have hq : 0 < b ⬝ᵥ (D⁻¹ *ᵥ b) := P6ebbe7d6.dot_pos hd _ _ hb hDb
  set w := D⁻¹ *ᵥ b with hw
  set q := b ⬝ᵥ w with hqdef
  set s := Real.sqrt (2 * c / (σ * q)) with hsdef
  set r := Real.sqrt (2 * c * σ / q) with hrdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 2 * c / (σ * q) := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = 2 * c * σ / q := Real.sq_sqrt (by positivity)
  have hs2' : s ^ 2 * (σ * q) = 2 * c := by rw [hs2]; field_simp
  have hr2' : r ^ 2 * q = 2 * c * σ := by rw [hr2]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hB : 0 < b ⬝ᵥ z := P6ebbe7d6.dot_pos hd _ _ hb hz
    have hQ := P6ebbe7d6.quad D hD b z (σ * s)
    rw [le_div_iff₀ hB]
    have e : c + 1 / (2 * σ) * (z ⬝ᵥ (D *ᵥ z)) = (2 * σ * c + z ⬝ᵥ (D *ᵥ z)) / (2 * σ) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [hQ, hs2']
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos hr0 (hDb i)
  · have eQ : (r • w) ⬝ᵥ (D *ᵥ (r • w)) = r ^ 2 * q := by
      rw [mulVec_smul, h1, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        dotProduct_comm]
      ring
    have eB : b ⬝ᵥ (r • w) = r * q := by
      rw [dotProduct_smul, smul_eq_mul]
    rw [eQ, eB]
    have hsr : s * r * q = 2 * c := by
      have : (s * r * q) ^ 2 = (2 * c) ^ 2 := by
        have : (s * r * q) ^ 2 = (s ^ 2 * (σ * q)) * (r ^ 2 * q) / σ := by
          field_simp
        rw [this, hs2', hr2']
        field_simp
      have h3 : 0 ≤ s * r * q := by positivity
      nlinarith [sq_nonneg (s * r * q - 2 * c), sq_nonneg (s * r * q + 2 * c)]
    rw [div_eq_iff (by positivity)]
    have : 1 / (2 * σ) * (r ^ 2 * q) = c := by
      rw [hr2']; field_simp
    rw [this]
    linarith [hsr]
