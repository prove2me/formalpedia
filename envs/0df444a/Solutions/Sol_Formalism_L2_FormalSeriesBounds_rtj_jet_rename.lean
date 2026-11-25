-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_jet_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:55.361007+00:00
-- url     : https://prove2.me/submissions/3043b865-5bc6-4f96-bc75-bd7371f2e410

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_subset
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_mfact_embDomain

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (e : σ ↪ τ) (P : MvPolynomial σ K) (F : MvPowerSeries σ K) :
    jetAt0 (MvPolynomial.rename e P) (MvPowerSeries.rename e F) = jetAt0 P F := by
  have hkey : ∀ d : σ →₀ ℕ, MvPowerSeries.coeff (Finsupp.embDomain e d) (MvPowerSeries.rename e F) =
      MvPowerSeries.coeff d F := by
    intro d
    rw [MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem d]
    · simp [Finsupp.embDomain_eq_mapDomain]
    · intro y hy hne
      exfalso
      apply hne
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
        Finsupp.embDomain_eq_mapDomain] at hy
      exact Finsupp.mapDomain_injective e.injective hy
  have hsupp : (MvPolynomial.rename e P).support ⊆ P.support.image (Finsupp.embDomain e) := by
    intro m hm
    obtain ⟨u, hu, hne⟩ := MvPolynomial.coeff_rename_ne_zero (⇑e) P m (MvPolynomial.mem_support_iff.mp hm)
    exact Finset.mem_image.mpr ⟨u, MvPolynomial.mem_support_iff.mpr hne, by
      rw [Finsupp.embDomain_eq_mapDomain]
      exact hu⟩
  rw [rtj_jet_subset _ _ _ hsupp, Finset.sum_image (by
    intro x _ y _ h
    exact Finsupp.embDomain_injective e h)]
  unfold jetAt0
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_rename_embDomain, rtj_mfact_embDomain, hkey]
end Formalism.L2.FormalSeriesBounds
