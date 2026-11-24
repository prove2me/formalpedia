-- Prove2me | solution 1 for Formalism.HN.HeightGram.gmat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:17.379656+00:00
-- url     : https://prove2.me/submissions/9e489b0a-bbae-4772-8d84-79452bc2b430

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
variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}
namespace Formalism.HN.HeightGram
theorem _root_.solution (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) (eS : S ≃ P × Fin 2) :
    (gmat lam G).submatrix (Equiv.prodCongr eS.symm (Equiv.refl (Fin j)))
        (Equiv.prodCongr eS.symm (Equiv.refl (Fin j))) =
      (kroneckerMap (· * ·) (amat lam eS) (1 : Matrix (Fin j) (Fin j) ℝ))ᵀ * bmat G *
        kroneckerMap (· * ·) (amat lam eS) (1 : Matrix (Fin j) (Fin j) ℝ) := by
  ext ⟨p, k⟩ ⟨q, k'⟩
  simp only [Matrix.submatrix_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, gmat,
    Matrix.of_apply]
  conv_rhs =>
    simp [amat, bmat, realif, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, ite_add_ite, Finset.sum_mul, Finset.mul_sum]
  first
  | (refine Finset.sum_congr rfl fun v _ => ?_
     simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
     ring)
  | (simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
     refine Finset.sum_congr rfl fun v _ => ?_
     ring)
end Formalism.HN.HeightGram
