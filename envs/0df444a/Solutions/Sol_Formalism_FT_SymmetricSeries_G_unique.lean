-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.G_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:47.216329+00:00
-- url     : https://prove2.me/submissions/530db432-1ffc-47cf-8512-60bde3aa9314

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_Eh_injective
import Theorems.Thm_Formalism_FT_SymmetricSeries_hasSubst_hv
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_prodpow_eq_zero
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_Eh
import Theorems.Thm_Formalism_FT_SymmetricSeries_mem_Aw

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
theorem _root_.solution (H : MvPowerSeries (Fin n) R) (hH : H.subst (hv R n) = 0) : H = 0 := by
  ext α
  rw [map_zero]
  obtain ⟨m, hm⟩ : ∃ m, wt α = m := ⟨_, rfl⟩
  let P : MvPolynomial (Fin n) R := ∑ β ∈ Aw n m, MvPolynomial.monomial β (MvPowerSeries.coeff β H)
  have hcP : ∀ β, MvPolynomial.coeff β P = if wt β = m then MvPowerSeries.coeff β H else 0 := by
    intro β
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases h : wt β = m
    · rw [if_pos ((mem_Aw m β).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((mem_Aw m β).mp h')), if_neg h]
  have hEP : Eh R n P = 0 := by
    ext d
    rw [MvPolynomial.coeff_zero, coeff_Eh]
    by_cases hd : d.degree = m
    · have h0 := congrArg (MvPowerSeries.coeff d) hH
      rw [MvPowerSeries.coeff_subst hasSubst_hv, map_zero] at h0
      refine Eq.trans ?_ h0
      apply finsum_congr
      intro β
      rw [hcP]
      by_cases hb : wt β = m
      · rw [if_pos hb]
      · rw [if_neg hb, zero_smul, coeff_prodpow_eq_zero β d (by rw [hd]; exact hb), smul_zero]
    · apply finsum_eq_zero_of_forall_eq_zero
      intro β
      rw [hcP]
      by_cases hb : wt β = m
      · rw [if_pos hb, coeff_prodpow_eq_zero β d (by rw [hb]; exact Ne.symm hd), smul_zero]
      · rw [if_neg hb, zero_smul]
  have hP0 : P = 0 := Eh_injective (by rw [hEP, map_zero])
  have h1 := hcP α
  rw [hP0, MvPolynomial.coeff_zero, if_pos hm] at h1
  exact h1.symm
end Formalism.FT.SymmetricSeries
