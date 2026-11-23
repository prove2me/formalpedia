-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.coeff_Fm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:45.066112+00:00
-- url     : https://prove2.me/submissions/e3ffade2-3086-4442-901f-91ad5016b33d

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
theorem _root_.solution (F : MvPowerSeries (Fin n) R) (m : ℕ) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d (Fm F m) = if d.degree = m then MvPowerSeries.coeff d F else 0 := by
  unfold Fm
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : d.degree = m
  · rw [if_pos h, if_pos]
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [← h, Finsupp.degree_eq_sum], Finset.subset_univ _⟩
  · rw [if_neg h, if_neg]
    rw [Finset.mem_finsuppAntidiag]
    rintro ⟨h1, _⟩
    exact h (by rw [Finsupp.degree_eq_sum]; exact h1)
end Formalism.FT.SymmetricSeries
