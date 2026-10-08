-- Prove2me | solution 1 for EulerMascheroni.Hankel.exists_int_poly_quadratic_decay
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T18:26:13.2881+00:00
-- url     : https://prove2.me/submissions/1ba91af0-e260-4aed-9a35-5727b21f3179
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HankelIrrationality_decay_of_normalized_family
import Theorems.Thm_EulerMascheroni_Hankel_gamma_affine_hankel_data

open Polynomial Filter Topology EulerMascheroni.Hankel

theorem solution :
    ∃ D : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ D * n ∧
      0 < aeval Real.eulerMascheroniConstant Q ∧
      aeval Real.eulerMascheroniConstant Q < Real.exp (-c * (n : ℝ) ^ 2) := by
  obtain ⟨D, h, a, b, m, κ, A, U, hκ, hAU, hh, hm, hPD, hint, hgrowth, hreal⟩ :=
    gamma_affine_hankel_data
  set γ := Real.eulerMascheroniConstant
  set F : ℕ → ℚ[X] := fun n => (hankelAffine (h n) (a n) (b n)).det with hF
  -- evaluation commutes with the determinant
  have heval : ∀ n, aeval γ (F n) =
      ((hankelAffine (h n) (a n) (b n)).map (fun p => aeval γ p)).det := by
    intro n
    simp only [hF]
    rw [AlgHom.map_det]
    rfl
  -- the determinant of an affine Hankel matrix has degree at most its size
  have hdeg : ∀ n, (F n).natDegree ≤ h n := by
    intro n
    have hM : hankelAffine (h n) (a n) (b n) =
        (X : ℚ[X]) • (Matrix.of fun i j : Fin (h n) => b n ((i : ℕ) + j)).map C +
          (Matrix.of fun i j : Fin (h n) => a n ((i : ℕ) + j)).map C := by
      ext i j
      simp only [hankelAffine, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.map_apply, smul_eq_mul]
      ring
    have := natDegree_det_X_add_C_le
      (Matrix.of fun i j : Fin (h n) => b n ((i : ℕ) + j))
      (Matrix.of fun i j : Fin (h n) => a n ((i : ℕ) + j))
    simp only [hF]
    rw [hM]
    simpa using this
  have hpos : ∀ᶠ n in atTop, 0 < aeval γ (F n) := by
    filter_upwards [hPD] with n hn
    rw [heval]
    exact hn.det_pos
  obtain ⟨c, hc, hdecay⟩ := HankelIrrationality.decay_of_normalized_family γ F m κ A U hκ hAU hm
    hint hgrowth hpos hreal
  refine ⟨D, c, hc, ?_⟩
  filter_upwards [hdecay] with n hn
  obtain ⟨Q, ⟨c', hc', hQ⟩, hQpos, hQlt⟩ := hn
  refine ⟨Q, ?_, hQpos, hQlt⟩
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have h1 : Q.natDegree = (Q.map (Int.castRingHom ℚ)).natDegree :=
    (natDegree_map_eq_of_injective hinj Q).symm
  rw [h1, hQ, natDegree_C_mul hc'.ne']
  exact (hdeg n).trans (hh n)
