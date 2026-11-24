-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BranchingSystems.sys_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:41.956139+00:00
-- url     : https://prove2.me/submissions/24a687db-771b-4c03-a420-7f3ea17f28c3

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_shf_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_shf_down
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_sdec_shf
import Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_fin_cap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp
import Theorems.Thm_Formalism_REAL_quantumDetHighestWeight_holds


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.FourierDecayAlt.P.BranchingSystems
theorem _root_.solution (hSM : ExistsSingMax) (hCS : CapSing) (hSR : SubRel) (hR : RaiseNZ) (hLo : LowerNZ)
    {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} {β : ℂ} {L : Fin (n + 1) → ℤ}
    (H : Hyp E β L) : Sys L (fun M => CapSp (subA E) (shf β M) ≠ ⊥) := by
  have gl' : GlRel (subA E) := (hSR (Module.End ℂ V) n E H.gl).1
  have hinj : ∀ M : Fin n → ℤ, CapSp (subA E) (shf β M) ≠ ⊥ → Function.Injective (shf β M) :=
    fun M hM => (hCS V n (subA E) _ gl' hM).1
  refine ⟨H.anti, ?_, ?_, ?_, ?_, fun M i => fin_cap (subA E) β M i⟩
  · intro M hM a b hab
    exact hinj M hM (by simp [shf, hab])
  · have := H.irr.1
    obtain ⟨ν, v, -, hv0, hHW, -⟩ := hSM V (n + 1) E H.gl ⊤ (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
    have hvL : v ∈ CapSp E (shf β L) := mem_CapSp.mpr fun w => H.cap w v
    have hne : CapSp E (shf β L) ≠ ⊥ := fun e => hv0 (by rw [e] at hvL; simpa using hvL)
    have hν := (hCS V (n + 1) E _ H.gl hne).2 (sdec_shf β H.anti) ν v hvL hv0 hHW
    have hHW' : IsHW (subA E) (fun k => ν k.castSucc) v :=
      ⟨fun a => hHW.1 a.castSucc, fun a b hab => hHW.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩
    have hmem : v ∈ CapSp (subA E) (shf β fun j => L j.castSucc) := by
      rw [mem_CapSp]
      intro w
      rw [quantumDetHighestWeight_holds V n (subA E) _ v gl' hHW' w]
      congr 1
      unfold cpol
      apply Finset.prod_congr rfl
      intro k _
      rw [hν]
      simp [shf]
    intro e
    rw [e] at hmem
    exact hv0 (by simpa using hmem)
  · intro M hM i hj
    have := hR V n E (shf β L) H.gl H.cap (shf β M) (hinj M hM) hM i
      (fun j e => hj j (by simpa [shf] using e))
    rwa [shf_up] at this
  · intro M hM i hj
    have := hLo V n E (shf β L) H.gl H.cap (shf β M) (hinj M hM) hM i (fun j e => hj j (by
      simp only [shf] at e
      have e2 : ((M i - 1 : ℤ) : ℂ) = (L j : ℂ) := by
        push_cast
        linear_combination e
      exact_mod_cast e2))
    rwa [shf_down] at this
end Formalism.FourierDecayAlt.P.BranchingSystems
