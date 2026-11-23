-- Prove2me | solution 1 for GenFrameSpan.SatP.Tmap_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:12.417853+00:00
-- url     : https://prove2.me/submissions/1c0c881e-0542-4f03-a203-b140c18faf7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open GenFrameSpan.SatP
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}
namespace GenFrameSpan.SatP
theorem _root_.solution (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (m : Lt × ℕ × Fin N0 →₀ ℕ) :
    Tmap π (monomial m 1) = ∏ s, rename (emb s) (π s (monomial (res s m) 1)) := by
  have : (monomial m (1 : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) =
      basisMonomials (Lt × ℕ × Fin N0) ℤ m := by
    rw [coe_basisMonomials]
  rw [this, Tmap, Module.Basis.constr_basis]
end GenFrameSpan.SatP
