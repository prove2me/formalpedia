-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_tri_succ_of_max_pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:46.310203+00:00
-- url     : https://prove2.me/submissions/7d30002c-0da3-465d-9155-405894baa0b8

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Theorems.Thm_Formalism_UG_P_fIwasawa_E_fix
import Theorems.Thm_Formalism_UG_P_fIwasawa_E_mulVec
import Theorems.Thm_Formalism_UG_P_fIwasawa_E_un
import Theorems.Thm_Formalism_UG_P_fIwasawa_H_single_left
import Theorems.Thm_Formalism_UG_P_fIwasawa_col_zero
import Theorems.Thm_Formalism_UG_P_fIwasawa_int_E
import Theorems.Thm_Formalism_UG_P_fIwasawa_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaStepB
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
private theorem fin_rev_between_of_between (ρ t : Fin n) (h1 : ρ < t) (h2 : t < Fin.rev ρ) :
    ρ < Fin.rev t ∧ Fin.rev t < Fin.rev ρ := by
  have ht := t.isLt
  simp only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 h2 ⊢
  omega
private theorem neg_mul_neg_div_self (a p : L) (hp : p ≠ 0) : -p * (-a / p) = a := by
  first
    | (rw [neg_mul_neg, mul_div_assoc']; exact mul_div_cancel_left₀ a hp)
    | (field_simp; done)
    | (field_simp; ring)
end FIwasawaStepB
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) (r : ℕ) (hT : fIwasawaTri r M)
    (ρ : Fin n) (hρr : ρ.val = r) (hρ : ρ < Fin.rev ρ) (hp : M ρ ρ ≠ 0)
    (hmax : ∀ i, ρ ≤ i → i ≤ Fin.rev ρ → Valued.v (M i ρ) ≤ Valued.v (M ρ ρ)) :
    ∃ k, fIwasawaKm σ k ∧ fIwasawaTri (r + 1) (k * M) := by
  have hne : ρ ≠ Fin.rev ρ := ne_of_lt hρ
  have hσp : σ (M ρ ρ) ≠ 0 := (map_ne_zero σ).mpr hp
  have hvp : Valued.v (M ρ ρ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp
  have hcz : ∀ i, Fin.rev ρ < i → M i ρ = 0 := fIwasawa_col_zero (σ := σ) M hM r hT ρ hρr hρ
  obtain ⟨z, hzeq⟩ : ∃ z : Fin n → L,
      z = fun t => if ρ < t ∧ t < Fin.rev ρ then -(M t ρ) / M ρ ρ else 0 := ⟨_, rfl⟩
  have hzout : ∀ t, ¬(ρ < t ∧ t < Fin.rev ρ) → z t = 0 := by
    intro t ht
    rw [hzeq]
    exact if_neg ht
  have hzsupp : ∀ t, z t ≠ 0 → ρ < t ∧ t < Fin.rev ρ := by
    intro t ht
    by_contra h
    exact ht (hzout t h)
  have hMz : ∀ t, ρ < t → t < Fin.rev ρ → M t ρ = -(M ρ ρ) * z t := by
    intro t h1 h2
    rw [hzeq]
    dsimp only
    rw [if_pos (And.intro h1 h2), neg_mul_neg_div_self _ _ hp]
  have hrevmid : ∀ j, ρ < Fin.rev j ∧ Fin.rev j < Fin.rev ρ → ρ < j ∧ j < Fin.rev ρ := by
    intro j h
    have h' := fin_rev_between_of_between ρ (Fin.rev j) h.1 h.2
    rwa [Fin.rev_rev] at h'
  obtain ⟨S, hSeq⟩ : ∃ S : L, S = fIwasawaH σ z z := ⟨_, rfl⟩
  have hzm : fIwasawaH σ z (fun k => M k ρ) = -(M ρ ρ) * S := by
    rw [hSeq]
    simp only [fIwasawaH]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hj : ρ < j ∧ j < Fin.rev ρ
    · rw [hMz j hj.1 hj.2]
      ring
    · rw [hzout (Fin.rev j) (fun h => hj (hrevmid j h)), map_zero σ]
      ring
  have hS : σ S = S := by
    rw [hSeq]
    simp only [fIwasawaH, map_sum, map_mul, hσ]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by
      simp only [Fin.revPerm_apply, Fin.rev_rev]
      ring)
  have key : ∀ j, σ (M (Fin.rev j) ρ) * M j ρ =
      ((if j = ρ then σ (M (Fin.rev ρ) ρ) * M ρ ρ else 0) +
        (if j = Fin.rev ρ then σ (M ρ ρ) * M (Fin.rev ρ) ρ else 0)) +
        σ (M ρ ρ) * M ρ ρ * (σ (z (Fin.rev j)) * z j) := by
    intro j
    rcases lt_trichotomy j ρ with h1 | h1 | h1
    · rw [hcz (Fin.rev j) (Fin.rev_lt_rev.mpr h1), map_zero σ, hzout j (fun h => lt_asymm h1 h.1),
        if_neg (ne_of_lt h1), if_neg (ne_of_lt (lt_trans h1 hρ))]
      ring
    · rw [h1, if_pos (rfl : ρ = ρ), if_neg hne, hzout ρ (fun h => lt_irrefl ρ h.1)]
      ring
    · rcases lt_trichotomy j (Fin.rev ρ) with h2 | h2 | h2
      · have hm := fin_rev_between_of_between ρ j h1 h2
        rw [hMz j h1 h2, hMz (Fin.rev j) hm.1 hm.2, if_neg (ne_of_gt h1), if_neg (ne_of_lt h2),
          map_mul σ, map_neg σ]
        ring
      · rw [h2, Fin.rev_rev, if_neg hne.symm, if_pos (rfl : Fin.rev ρ = Fin.rev ρ),
          hzout (Fin.rev ρ) (fun h => lt_irrefl (Fin.rev ρ) h.2)]
        ring
      · rw [hcz j h2, hzout j (fun h => lt_asymm h2 h.2), if_neg (ne_of_gt h1),
          if_neg (ne_of_gt h2)]
        ring
  have hA : σ (M (Fin.rev ρ) ρ) * M ρ ρ + σ (M ρ ρ) * M (Fin.rev ρ) ρ +
      σ (M ρ ρ) * M ρ ρ * S = 0 := by
    have hiso := fIwasawa_iso (σ := σ) M hM ρ hρ
    rw [Fintype.sum_congr _ _ key] at hiso
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, ← Finset.mul_sum] at hiso
    rw [hSeq]
    simpa only [fIwasawaH] using hiso
  obtain ⟨c, hceq⟩ : ∃ c : L, c = -S - M (Fin.rev ρ) ρ / M ρ ρ := ⟨_, rfl⟩
  have hc0 : c + σ c + fIwasawaH σ z z = 0 := by
    rw [← hSeq, hceq, map_sub σ, map_neg σ, map_div₀ σ, hS]
    field_simp
    first
      | linear_combination hA
      | linear_combination -hA
      | linear_combination (-1 : L) * hA
  have hzv : ∀ i, Valued.v (z i) ≤ 1 := by
    intro i
    by_cases h : ρ < i ∧ i < Fin.rev ρ
    · have h1 := hmax i (le_of_lt h.1) (le_of_lt h.2)
      rw [hMz i h.1 h.2, Valuation.map_mul, Valuation.map_neg] at h1
      calc Valued.v (z i) = (Valued.v (M ρ ρ))⁻¹ * (Valued.v (M ρ ρ) * Valued.v (z i)) :=
            (inv_mul_cancel_left₀ hvp _).symm
        _ ≤ (Valued.v (M ρ ρ))⁻¹ * Valued.v (M ρ ρ) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvp
    · rw [hzout i h, Valuation.map_zero]
      first | exact zero_le' | exact zero_le _ | simp
  have hSv : Valued.v S ≤ 1 := by
    rw [hSeq]
    simp only [fIwasawaH]
    refine Valuation.map_sum_le _ (fun j _ => ?_)
    rw [Valuation.map_mul, hσv]
    calc Valued.v (z (Fin.rev j)) * Valued.v (z j) ≤ 1 * 1 := by
          first | exact mul_le_one' (hzv _) (hzv _) | (gcongr <;> exact hzv _)
      _ = 1 := mul_one 1
  have hcv : Valued.v c ≤ 1 := by
    have hb := hmax (Fin.rev ρ) (le_of_lt hρ) le_rfl
    have hbp : Valued.v (M (Fin.rev ρ) ρ / M ρ ρ) ≤ 1 := by
      rw [map_div₀, div_eq_mul_inv]
      calc Valued.v (M (Fin.rev ρ) ρ) * (Valued.v (M ρ ρ))⁻¹
          ≤ Valued.v (M ρ ρ) * (Valued.v (M ρ ρ))⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvp
    have h1 : Valued.v (-S) ≤ 1 := by
      rw [Valuation.map_neg]
      exact hSv
    rw [hceq]
    first
      | exact Valuation.map_sub_le _ h1 hbp
      | exact le_trans (Valuation.map_sub _ _ _) (max_le h1 hbp)
  have he : ∀ i, Valued.v ((Pi.single (Fin.rev ρ) (1 : L) : Fin n → L) i) ≤ 1 := by
    intro i
    by_cases h : i = Fin.rev ρ
    · (rw [h, Pi.single_eq_same, Valuation.map_one]) <;> exact le_rfl
    · rw [Pi.single_eq_of_ne h, Valuation.map_zero]
      first | exact zero_le' | exact zero_le _ | simp
  have hee : fIwasawaH σ (Pi.single (Fin.rev ρ) (1 : L)) (Pi.single (Fin.rev ρ) (1 : L)) = 0 := by
    rw [fIwasawa_H_single_left (σ := σ), Fin.rev_rev, Pi.single_eq_of_ne hne]
  have hez : fIwasawaH σ (Pi.single (Fin.rev ρ) (1 : L)) z = 0 := by
    rw [fIwasawa_H_single_left (σ := σ), Fin.rev_rev]
    exact hzout ρ (fun h => lt_irrefl ρ h.1)
  have hcol : ∀ (A : Matrix (Fin n) (Fin n) L) (i j : Fin n),
      (A * M) i j = (A *ᵥ fun k => M k j) i := by
    intro A i j
    first
      | rfl
      | simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      | simp [Matrix.mul_apply, Matrix.mulVec, Matrix.dotProduct]
  refine ⟨fIwasawaE σ (Pi.single (Fin.rev ρ) 1) z c,
    And.intro (fIwasawa_E_un (σ := σ) hσ _ z c hee hez hc0)
      (fIwasawa_int_E (σ := σ) hσv _ z c he hzv hcv), ?_⟩
  intro i j hj hji
  rw [hcol]
  by_cases hj' : j.val < r
  · have hjρ : j < ρ := by
      rw [Fin.lt_iff_val_lt_val, hρr]
      exact hj'
    rw [fIwasawa_E_fix (σ := σ) ρ z c hzsupp (fun k => M k j) (hT ρ j hj' hjρ)
      (fun t h1 _ => hT t j hj' (lt_trans hjρ h1))]
    exact hT i j hj' hji
  · have hjρ : j = ρ := Fin.ext (by omega)
    rw [hjρ] at hji ⊢
    rw [fIwasawa_E_mulVec (σ := σ), fIwasawa_H_single_left (σ := σ), Fin.rev_rev, hzm]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_trichotomy i (Fin.rev ρ) with h | h | h
    · rw [Pi.single_eq_of_ne (ne_of_lt h), hMz i hji h]
      ring
    · rw [h, Pi.single_eq_same, hzout (Fin.rev ρ) (fun h' => lt_irrefl (Fin.rev ρ) h'.2), hceq]
      first
        | (field_simp; ring)
        | (field_simp; done)
        | (simp only [mul_zero, mul_one, add_zero]; field_simp; ring)
    · rw [Pi.single_eq_of_ne (ne_of_gt h), hcz i h, hzout i (fun h' => lt_asymm h h'.2)]
      ring
end Formalism.UG.P
