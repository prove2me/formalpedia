-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.prodpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.845691+00:00
-- url     : https://prove2.me/submissions/39644eff-5b4d-411a-9e39-eec89d7fadf5

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.FT Formalism.FT.SymmetricSeries
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.FT.SymmetricSeries
theorem _root_.solution (α : Fin n →₀ ℕ) : α.prod (fun j e => hv R n j ^ e) =
    ((∏ j : Fin n, (MvPolynomial.hsymm (Fin n) R (j + 1)) ^ (α j) : MvPolynomial (Fin n) R) :
      MvPowerSeries (Fin n) R) := by
  unfold hv Formalism.FT.hPS
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have h := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := R))
    (fun j : Fin n => MvPolynomial.hsymm (Fin n) R (j + 1) ^ α j) univ
  simp only [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply] at h
  exact h.symm
end Formalism.FT.SymmetricSeries
