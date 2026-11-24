-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_decomp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:21:10.717674+00:00
-- url     : https://prove2.me/submissions/95fb6d63-4b55-4567-a574-48fdea7e8395

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_Sys_box
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_Sys_noUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_Sys_noDown
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_shf_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_shf_down
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_sys_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr BranchingSystems
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.ExistsSingMax → Qr.CapSing → Qr.CapStab → Qr.SubRel → Qr.CovUp → Qr.VecDown →
    Qr.RaiseNZ → Qr.LowerNZ → Qr.Decomp := by
  intro hSM hCS hSt hSR hCU hVD hR hLo V _ _ _ n E β L H
  have S := sys_of hSM hCS hSR hR hLo H
  obtain ⟨gl', hcov, hvec, -, hyy, hnn⟩ := hSR (Module.End ℂ V) n E H.gl
  refine ⟨fun M hM => S.box M hM, ?_⟩
  set V' : Submodule ℂ V := ⨆ (M : Fin n → ℤ) (_ : Box L M), CapSp (subA E) (shf β M) with hV'
  have hle : ∀ M, Box L M → CapSp (subA E) (shf β M) ≤ V' := fun M hM =>
    le_iSup₂ (f := fun (M : Fin n → ℤ) (_ : Box L M) => CapSp (subA E) (shf β M)) M hM
  have hstab : Stab E V' := by
    intro a b
    suffices h : V' ≤ V'.comap (E a b) from fun v hv => h hv
    refine iSup₂_le fun M hM v hv => ?_
    rw [Submodule.mem_comap]
    have hMinj : Function.Injective (shf β M) := (hCS V n (subA E) _ gl' (S.box M hM)).1
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => exact hle M hM ((hSt V n (subA E) _ gl').2 _ hnn v hv)
      | cast x =>
        obtain ⟨Φ, h1, h2, -⟩ := hVD V n (subA E) (yK E) gl' hvec hyy (shf β M) hMinj v hv
        change yK E x v ∈ V'
        rw [← h1 x]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h3 := h2 i x
        rw [shf_down] at h3
        by_cases hi : M i = L i.succ + 1
        · have := not_not.mp (S.noDown M hM i hi)
          rw [this] at h3
          rw [(Submodule.mem_bot ℂ).mp h3]
          exact Submodule.zero_mem _
        · refine hle _ ?_ h3
          intro j
          by_cases hj : j = i
          · subst hj
            have := hM j
            simp only [Function.update_self]
            omega
          · rw [Function.update_of_ne hj]
            exact hM j
    | cast y =>
      induction b using Fin.lastCases with
      | last =>
        obtain ⟨Ψ, h1, h2, -⟩ := hCU V n (subA E) (etaK E) gl' hcov (shf β M) hMinj v hv
        change etaK E y v ∈ V'
        rw [← h1 y]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h3 := h2 i y
        rw [shf_up] at h3
        by_cases hi : M i = L i.castSucc
        · have := not_not.mp (S.noUp M hM i hi)
          rw [this] at h3
          rw [(Submodule.mem_bot ℂ).mp h3]
          exact Submodule.zero_mem _
        · refine hle _ ?_ h3
          intro j
          by_cases hj : j = i
          · subst hj
            have := hM j
            simp only [Function.update_self]
            omega
          · rw [Function.update_of_ne hj]
            exact hM j
      | cast x => exact hle M hM ((hSt V n (subA E) _ gl').1 y x v hv)
  rcases H.irr.2 V' hstab with h | h
  · exfalso
    have hB : Box L (fun j => L j.castSucc) := fun j => ⟨H.anti (Fin.castSucc_lt_succ), le_rfl⟩
    exact S.top (le_bot_iff.mp (h ▸ hle _ hB))
  · exact h
end Formalism.FourierDecayAlt.P
