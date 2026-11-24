-- Prove2me | solution 1 for Formalism.UG.P.herm_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:11.423996+00:00
-- url     : https://prove2.me/submissions/24c6d2b1-1fbb-45c0-bc0e-b892ae22f779

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Theorems.Thm_Formalism_UG_P_star_scal
import Theorems.Thm_Formalism_UG_P_scal_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix
namespace Formalism.UG.P
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) :
    ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues))ᴴ * J *
        ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues)) =
      diagonal (fun i => ((hJ.eigenvalues i / |hJ.eigenvalues i| : ℝ) : ℂ)) := by
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_scal]
  have hU : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hJ.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hJ.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J * (hJ.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (RCLike.ofReal ∘ hJ.eigenvalues) := by
    have h1 := congrArg (fun M => ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * M *
      (hJ.eigenvectorUnitary : Matrix n n ℂ)) hJ.spectral_theorem
    first
      | simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h1
      | simp only [Unitary.conjStarAlgAut, Matrix.star_eq_conjTranspose] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  calc _ = diagonal (scal hJ.eigenvalues) * (((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J *
          (hJ.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (scal hJ.eigenvalues) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        exact scal_sq _ i
end Formalism.UG.P
