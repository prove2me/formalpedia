-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_prod_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:05.196284+00:00
-- url     : https://prove2.me/submissions/6ca4eaa8-d195-4a42-9cfe-8dfdcc20f001

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_eqv_embDomain
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_atP_single
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_atP_eq_zero
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_prod_atP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
section Alg
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
variable [Fintype Pl]
variable [DecidableEq Pl]
private theorem coe_rename_sigma_mk_eq_atP (v : Pl) (p : MvPolynomial (ι v) K) :
    ((MvPolynomial.rename (Sigma.mk v) p : MvPolynomial (Σ v, ι v) K) : MvPowerSeries (Σ v, ι v) K) =
      atP v (p : MvPowerSeries (ι v) K) := by
  ext d
  rw [MvPolynomial.coeff_coe]
  by_cases h : ∃ m, d = eqv.symm (Pi.single v m)
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_atP_single, MvPolynomial.coeff_coe]
    have h2 : eqv.symm (Pi.single v m) = Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
      rw [AddEquiv.symm_apply_eq, eqv_embDomain]
    rw [h2]
    exact MvPolynomial.coeff_rename_embDomain (Function.Embedding.sigmaMk v) p m
  · push_neg at h
    rw [coeff_atP_eq_zero v _ d h]
    apply MvPolynomial.coeff_rename_eq_zero
    intro u hu
    exfalso
    refine h u ?_
    rw [← hu, eq_comm, AddEquiv.symm_apply_eq, ← eqv_embDomain v u]
    exact congrArg eqv (Finsupp.embDomain_eq_mapDomain (Function.Embedding.sigmaMk v) u)
end Alg
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
variable [Fintype Pl]
variable [DecidableEq Pl]
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution (P : ∀ v, MvPolynomial (ι v) K) (n : (Σ v, ι v) →₀ ℕ) :
    MvPolynomial.coeff n (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) =
      ∏ v, MvPolynomial.coeff (eqv n v) (P v) := by
  have h1 : ((∏ v, MvPolynomial.rename (Sigma.mk v) (P v) : MvPolynomial (Σ v, ι v) K) :
      MvPowerSeries (Σ v, ι v) K) = ∏ v, atP v (P v : MvPowerSeries (ι v) K) := by
    rw [← Finset.prod_congr rfl fun v _ => coe_rename_sigma_mk_eq_atP v (P v)]
    exact map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (R := K)) _ _
  rw [← MvPolynomial.coeff_coe, h1, coeff_prod_atP]
  simp only [MvPolynomial.coeff_coe]
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
