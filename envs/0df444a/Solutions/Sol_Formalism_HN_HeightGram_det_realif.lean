-- Prove2me | solution 1 for Formalism.HN.HeightGram.det_realif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:08.966176+00:00
-- url     : https://prove2.me/submissions/dd34e273-22d7-48ea-88bb-98a638c79320

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.HN.HeightGram
theorem _root_.solution (G : Matrix n n ℂ) : (realif G).det = Complex.normSq G.det := by
  let e : Fin 2 × n ≃ n ⊕ n :=
    { toFun := fun p => if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
      invFun := fun s => Sum.elim (fun i => ((0 : Fin 2), i)) (fun i => ((1 : Fin 2), i)) s
      left_inv := by
        rintro ⟨k, i⟩
        fin_cases k <;> rfl
      right_inv := by
        rintro (i | i) <;> rfl }
  let Gre : Matrix n n ℂ := G.map fun z => ((z.re : ℝ) : ℂ)
  let Gim : Matrix n n ℂ := G.map fun z => ((z.im : ℝ) : ℂ)
  let R : Matrix (n ⊕ n) (n ⊕ n) ℂ := ((realif G).map Complex.ofRealHom).submatrix e.symm e.symm
  have hR : R = Matrix.fromBlocks Gre (-Gim) Gim Gre := by
    ext (i | i) (j | j) <;> simp [R, e, Gre, Gim, realif]
  let U : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks 1 1 ((-Complex.I) • (1 : Matrix n n ℂ)) (Complex.I • (1 : Matrix n n ℂ))
  let D : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks G 0 0 (G.map star)
  have hRU : R * U = U * D := by
    rw [hR]
    simp only [U, D, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.mul_smul, Matrix.smul_mul, add_zero, zero_add]
    congr 1 <;> ext i j <;> apply Complex.ext <;> simp [Gre, Gim]
  have hU : U.det ≠ 0 := by
    simp only [U, Matrix.det_fromBlocks_one₁₁, Matrix.mul_one]
    rw [neg_smul, sub_neg_eq_add, ← add_smul, Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ ?_
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hdet : R.det = D.det := by
    have h := congrArg Matrix.det hRU
    rw [Matrix.det_mul, Matrix.det_mul] at h
    exact mul_right_cancel₀ hU (h.trans (mul_comm _ _))
  have hD : D.det = G.det * star G.det := by
    have hc : G.map star = Gᴴᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [D, Matrix.det_fromBlocks_zero₂₁, hc, Matrix.det_transpose, Matrix.det_conjTranspose]
  have hR' : R.det = ((realif G).det : ℂ) := by
    simp only [R, Matrix.det_submatrix_equiv_self]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  apply Complex.ofReal_injective
  rw [← hR', hdet, hD, Complex.star_def, Complex.mul_conj]
end Formalism.HN.HeightGram
