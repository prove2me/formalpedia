-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.fam_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:06:05.324535+00:00
-- url     : https://prove2.me/submissions/4310dc11-a771-459c-915b-1ef68e95dd3c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_capelli_singular


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
theorem _root_.solution [FiniteDimensional ℂ V] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ V) (hF : GlRel F) (m : Fin n → ℂ)
    (hm : SDec m) (i : Fin n) (Φ : Fin n → V) (hmem : ∀ c, Φ c ∈ CapSp F m)
    (hd : ∀ a c, F a a (Φ c) = (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) • Φ c)
    (hr : ∀ a b c, a < b → F a b (Φ c) = if a = c then -(Φ b) else 0) (h0 : Φ i = 0) : ∀ c, Φ c = 0 := by
  classical
  by_contra hne
  rw [not_forall] at hne

  obtain ⟨c0, hc0⟩ := hne
  let S := Finset.univ.filter (fun c => Φ c ≠ 0)
  have hS : S.Nonempty := ⟨c0, by simp [S, hc0]⟩
  have hcS : Φ (S.max' hS) ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hbig : ∀ b, S.max' hS < b → Φ b = 0 := by
    intro b hb
    by_contra hb0
    exact absurd (S.le_max' b (by simp [S, hb0])) (not_le.mpr hb)
  have hHW : IsHW F (fun a => m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) -
      if a = S.max' hS then 1 else 0) (Φ (S.max' hS)) := by
    refine ⟨fun a => hd a _, fun a b hab => ?_⟩
    rw [hr a b _ hab]
    split_ifs with hac
    · subst hac
      rw [hbig b hab, neg_zero]
    · rfl
  have hne' : CapSp F m ≠ ⊥ := by
    intro h
    have hm0 := hmem (S.max' hS)
    rw [h] at hm0
    exact hcS ((Submodule.mem_bot ℂ).mp hm0)

  have hw := (Formalism.FourierDecayAlt.P.capelli_singular V n F m hF hne').2 hm _ _ (hmem _) hcS hHW
  by_cases hic : i = S.max' hS
  · exact hcS (hic ▸ h0)
  · have := hw i
    simp [hic] at this
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
