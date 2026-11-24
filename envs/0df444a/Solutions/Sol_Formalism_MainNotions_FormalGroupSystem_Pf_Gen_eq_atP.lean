-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.Gen.eq_atP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:59:13.542842+00:00
-- url     : https://prove2.me/submissions/97154684-864c-4146-b7d5-000e8cb6de18

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_mem_SuppOn
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_resP
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_atP_eq_zero
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_atP_single
import Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_eqv_embDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
theorem _root_.solution {R Pl : Type} [CommRing R] {ι : Pl → Type} [Fintype Pl] [DecidableEq Pl] (v : Pl)
    (f : MvPowerSeries (Σ v, ι v) R) (hf : f ∈ SuppOn (Sigma.fst : (Σ v, ι v) → Pl) v) :
    f = atP v (resP v f) := by
  classical
  ext n
  have h2 : ∀ m : ι v →₀ ℕ, (eqv (ι := ι)).symm (Pi.single v m) =
      Finsupp.embDomain (Function.Embedding.sigmaMk v) m := by
    intro m
    rw [AddEquiv.symm_apply_eq, eqv_embDomain]
  by_cases hn : MvPowerSeries.coeff n f = 0
  · rw [hn]
    by_cases h : ∃ m, n = eqv.symm (Pi.single v m)
    · obtain ⟨m, rfl⟩ := h
      rw [coeff_atP_single, coeff_resP, ← h2]
      exact hn.symm
    · push_neg at h
      exact (coeff_atP_eq_zero v _ n h).symm
  · have hsupp := (mem_SuppOn.mp hf) n hn
    have hn' : n = eqv.symm (Pi.single v (eqv n v)) := by
      rw [AddEquiv.eq_symm_apply]
      funext w
      ext i
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hw, Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply]
        by_contra hne
        exact hw (hsupp ⟨w, i⟩ (Finsupp.mem_support_iff.mpr hne))
    calc MvPowerSeries.coeff n f
        = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) (eqv n v)) f := by
          rw [← h2, ← hn']
      _ = MvPowerSeries.coeff n (atP v (resP v f)) := by
          rw [← coeff_resP, ← coeff_atP_single v (resP v f) (eqv n v), ← hn']
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen
