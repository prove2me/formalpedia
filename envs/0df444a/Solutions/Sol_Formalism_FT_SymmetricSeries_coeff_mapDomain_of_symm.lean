-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.coeff_mapDomain_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:51.313805+00:00
-- url     : https://prove2.me/submissions/9391afb6-5525-402c-baea-8d543b513ed8

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_prod_X_perm

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
theorem _root_.solution (F : MvPowerSeries (Fin n) R)
    (hF : ∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F)
    (π : Equiv.Perm (Fin n)) (d : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (d.mapDomain π) F = MvPowerSeries.coeff d F := by
  have hs : MvPowerSeries.HasSubst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => MvPowerSeries.constantCoeff_X _)
  have h := congrArg (MvPowerSeries.coeff (d.mapDomain π)) (hF π)
  rw [MvPowerSeries.coeff_subst hs] at h
  simp_rw [prod_X_perm, MvPowerSeries.coeff_monomial,
    (Finsupp.mapDomain_injective π.injective).eq_iff, smul_ite, smul_zero, smul_eq_mul, mul_one] at h
  rw [← h, finsum_eq_single _ d (fun e he => if_neg (Ne.symm he))]
  simp
end Formalism.FT.SymmetricSeries
