-- Prove2me | solution 1 for Formalism.UG.P.fSatake_tMat_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:17.936347+00:00
-- url     : https://prove2.me/submissions/1045a220-bc74-427d-94cd-f24e707f5665

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    (a : Fin m → ℤ) : ∃ t : GU σ n, ⟪t⟫ = tMat ϖ n m a := by
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  have hσ : σ ϖ = ϖ := by
    obtain ⟨-, -, h, -⟩ := hU
    exact h
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have key : ∀ i j : Fin n, (i : ℕ) + j + 1 = n → tMat ϖ n m a i i * tMat ϖ n m a j j = 1 := by
    intro i j hij
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> first
      | omega
      | (simp; done)
      | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [add_neg_eq_zero]; congr 1;
          simp only [Fin.mk.injEq]; omega)
      | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [neg_add_eq_zero]; congr 1;
          simp only [Fin.mk.injEq]; omega)
  have hne : ∀ i, tMat ϖ n m a i i ≠ 0 := fun i h => by
    have hi := i.isLt
    have h2 := key i ⟨n - 1 - i, by omega⟩ (by show (i : ℕ) + (n - 1 - (i : ℕ)) + 1 = n; omega)
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hσd : ∀ i, σ (tMat ϖ n m a i i) = tMat ϖ n m a i i := by
    intro i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> simp [map_zpow₀, hσ]
  have hdiag : tMat ϖ n m a = Matrix.diagonal (fun i => tMat ϖ n m a i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.diagonal_apply_ne _ h, tMat, Matrix.diagonal_apply_ne _ h]
  have hinv1 : tMat ϖ n m a * Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹) = 1 := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact mul_inv_cancel₀ (hne i)
    · rw [if_neg h, tMat, Matrix.diagonal_apply_ne _ h, zero_mul]
  have hinv2 : Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹) * tMat ϖ n m a = 1 := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact inv_mul_cancel₀ (hne i)
    · rw [if_neg h, tMat, Matrix.diagonal_apply_ne _ h, mul_zero]
  refine ⟨⟨⟨tMat ϖ n m a, Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹), hinv1, hinv2⟩, ?_⟩, rfl⟩
  show cT σ (tMat ϖ n m a) * antiJ L n * tMat ϖ n m a = antiJ L n
  rw [hdiag, cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hσd]
  rw [antiJ]
  split_ifs with h
  · rw [mul_one]
    exact key i j h
  · simp
end Formalism.UG.P
