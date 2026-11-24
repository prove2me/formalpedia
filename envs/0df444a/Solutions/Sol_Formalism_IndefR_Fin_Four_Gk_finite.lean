-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.Gk_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:51.656008+00:00
-- url     : https://prove2.me/submissions/5cf2797a-e45b-41ca-8a27-99b317ad158a

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_out
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y))) (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
    {k : ℕ} (hk : 0 < k) : Finite (Gk L Y k) := by
  haveI := hfinY k hk
  refine Finite.of_injective (fun g : Gk L Y k =>
    (QuotientAddGroup.mk (⟨k • (g : QY L Y).out,
      AddSubgroup.mem_inf.mpr ⟨(Gk_out g).2, nsmul_mem (Gk_out g).1 k⟩⟩ : ↥(L ⊓ Y)) : Qt k (L ⊓ Y))) ?_
  intro g₁ g₂ he
  have he' := QuotientAddGroup.eq.mp he
  rw [AddSubgroup.mem_addSubgroupOf] at he'
  have hm : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out) ∈ smulSub k (L ⊓ Y) := by
    convert he' using 1
    simp [smul_add, smul_neg]
  obtain ⟨m, hmm, hkm⟩ := AddSubgroup.mem_map.mp hm
  have key : -(g₁ : QY L Y).out + (g₂ : QY L Y).out = m := by
    have h0 : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out - m) = 0 := by
      rw [smul_sub]
      exact sub_eq_zero.mpr hkm.symm
    exact sub_eq_zero.mp (htf k hk _ h0)
  apply Subtype.ext
  have e1 := QuotientAddGroup.out_eq' (g₁ : QY L Y)
  have e2 := QuotientAddGroup.out_eq' (g₂ : QY L Y)
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact QuotientAddGroup.eq.mpr (by rw [key]; exact hmm)
end Formalism.IndefR.Fin.Four
