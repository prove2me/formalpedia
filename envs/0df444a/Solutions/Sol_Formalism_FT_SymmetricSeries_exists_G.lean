-- Prove2me | solution 1 for Formalism.FT.SymmetricSeries.exists_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:59.649307+00:00
-- url     : https://prove2.me/submissions/bcc01528-4629-4827-b5a5-f81c52fc205f

import Definitions.Def_Formalism_ArtinHasse_Statement
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Theorems.Thm_Formalism_FT_SymmetricSeries_Eh_surj
import Theorems.Thm_Formalism_FT_SymmetricSeries_hasSubst_hv
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_prodpow_eq_zero
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_Eh
import Theorems.Thm_Formalism_FT_SymmetricSeries_coeff_Fm
import Theorems.Thm_Formalism_FT_SymmetricSeries_Fm_symm

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
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F) :
    ∃ G : MvPowerSeries (Fin n) R, G.subst (hv R n) = F := by
  choose q hq using fun m => Eh_surj (Fm F m) (Fm_symm F hF m)
  let G : MvPowerSeries (Fin n) R := fun α => MvPolynomial.coeff α (q (wt α))
  refine ⟨G, ?_⟩
  ext d
  rw [MvPowerSeries.coeff_subst hasSubst_hv G d]
  have h2 : MvPowerSeries.coeff d F = MvPolynomial.coeff d (Eh R n (q d.degree)) := by
    rw [hq, coeff_Fm, if_pos rfl]
  rw [h2, coeff_Eh]
  apply finsum_congr
  intro α
  by_cases h : wt α = d.degree
  · show MvPolynomial.coeff α (q (wt α)) • _ = _
    rw [h]
  · rw [coeff_prodpow_eq_zero α d h, smul_zero, smul_zero]
end Formalism.FT.SymmetricSeries
