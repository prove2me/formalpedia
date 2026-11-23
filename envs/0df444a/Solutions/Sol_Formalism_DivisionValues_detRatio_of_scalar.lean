-- Prove2me | solution 1 for Formalism.DivisionValues.detRatio_of_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:06.801804+00:00
-- url     : https://prove2.me/submissions/306a48f5-4d38-4a6e-b9a7-efa5dcf7d944

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Theorems.Thm_Formalism_DivisionValues_star_mulVec_dot
import Theorems.Thm_Formalism_DivisionValues_majAt_eq
import Theorems.Thm_Formalism_DivisionValues_cv_mulVec
import Theorems.Thm_Formalism_DivisionValues_detRatio_eq
import Theorems.Thm_Formalism_DivisionValues_metMat_det_re_ne
import Theorems.Thm_Formalism_DivisionValues_det_of_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution (v : InfinitePlace K) {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hS : IsUnit (XS v).det)
    (φ : Matrix (Fin d) (Fin d) K) {Ix : Type} [Fintype Ix]
    (Qp : Ix → Submodule K (Fin d → K)) (hind : iSupIndep Qp) (htop : (⨆ p, Qp p) = ⊤)
    (c : Ix → ℝ)
    (h : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin d → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v (φ.mulVec x) (φ.mulVec y) =
        ((c p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XS v x y) :
    detRatio XS XT φ v = ∏ p, c p ^ finrank K (Qp p) ∧ ∑ p, finrank K (Qp p) = d := by
  obtain ⟨hdet, hsum⟩ := det_of_scalar v.embedding Qp hind htop
    ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding) (metMat XS v)
    (fun p => ((c p : ℝ) : ℂ)) (by
      intro p x hx y
      rw [← star_mulVec_dot, ← cv_mulVec, ← cv_mulVec, ← majAt_eq, ← majAt_eq]
      exact h p x hx y)
  refine ⟨?_, hsum⟩
  rw [detRatio_eq, hdet]
  have hm := metMat_det_re_ne XS v hS
  have hc : (∏ p, ((c p : ℝ) : ℂ) ^ finrank K (Qp p)) =
      ((∏ p, c p ^ finrank K (Qp p) : ℝ) : ℂ) := by
    simp [Complex.ofReal_prod]
  rw [hc, Complex.re_ofReal_mul]
  field_simp
end Formalism.DivisionValues
