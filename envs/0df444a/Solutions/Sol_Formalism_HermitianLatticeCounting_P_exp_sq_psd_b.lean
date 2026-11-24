-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.exp_sq_psd_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:34.927141+00:00
-- url     : https://prove2.me/submissions/95e90191-fd33-4da2-94f2-8c6497c96be3

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eigenvalue_le_hs_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) :
    ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - NormedSpace.exp X * NormedSpace.exp X).PosSemidef := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Fin N → ℂ := RCLike.ofReal ∘ hX.eigenvalues with hDdef
  have hUU : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hX.eigenvectorUnitary
  have hUU' : Uᴴ * U = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hspec : X = U * diagonal D * Uᴴ := by
    conv_lhs => rw [hX.spectral_theorem]
    simp [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hUU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU, hUU'⟩, rfl⟩
  have hexp : NormedSpace.exp X = U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hspec, ← hinv, Matrix.exp_conj U _ hunit, Matrix.exp_diagonal]
    have hD : NormedSpace.exp D = fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ) := by
      funext i
      rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
      rfl
    rw [hD, hinv]
  have e : ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - NormedSpace.exp X * NormedSpace.exp X)
      = U * diagonal (fun i => ((Real.exp (hs X) ^ 2 - Real.exp (hX.eigenvalues i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hexp]
    have e1 : U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ *
        (U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ)
        = U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
        diagonal_mul_diagonal]
      congr 3
      ext i
      push_cast; ring
    have e2 : ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ))
        = U * diagonal (fun _ => ((Real.exp (hs X) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      have : diagonal (fun _ : Fin N => ((Real.exp (hs X) ^ 2 : ℝ) : ℂ))
          = ((Real.exp (hs X) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
        ext a b; simp [diagonal_apply, one_apply]
      rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
      ext a b; simp
    rw [e1, e2, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 3
    ext i
    push_cast; ring
  rw [e]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  rw [Complex.zero_le_real, sub_nonneg]
  gcongr
  exact eigenvalue_le_hs_b X hX i
end Formalism.HermitianLatticeCounting.P
