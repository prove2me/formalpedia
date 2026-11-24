-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:17:44.86789+00:00
-- url     : https://prove2.me/submissions/008039d5-4ea4-493d-a77f-c9f9cd636235

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_le_Cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_Cl_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_Cl_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (T L : Fin N → Fin N → Prop)
    (M : Submodule ℂ V)
    (h0 : ∀ a b, T a b → ∀ m ∈ M, E a b m ∈ Cl E L M)
    (h1 : ∀ a b c d, T a b → L c d → b = c → T a d ∨ L a d)
    (h2 : ∀ a b c d, T a b → L c d → d = a → T c b ∨ L c b) :
    ∀ a b, T a b → ∀ q ∈ Cl E L M, E a b q ∈ Cl E L M := by
  have key : Cl E L M ≤ Cl E L M ⊓ ⨅ a, ⨅ b, ⨅ (_ : T a b), (Cl E L M).comap (E a b) := by
    apply Cl_le
    · intro m hm
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      exact ⟨le_Cl E L M hm, fun a b hab => h0 a b hab m hm⟩
    · intro c d hcd q hq
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hq ⊢
      obtain ⟨hq1, hq2⟩ := hq
      refine ⟨Cl_closed c d hcd q hq1, fun a b hab => ?_⟩
      have hc := hE a b c d
      have e : E a b (E c d q) = E c d (E a b q) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) q := by
        rw [← hc]
        simp only [LinearMap.sub_apply, Module.End.mul_apply]
        abel
      rw [e]
      refine Submodule.add_mem _ (Cl_closed c d hcd _ (hq2 a b hab)) ?_
      rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs with hbc
        · rcases h1 a b c d hab hcd hbc with h | h
          · exact hq2 a d h
          · exact Cl_closed a d h q hq1
        · simp
      · split_ifs with hda
        · rcases h2 a b c d hab hcd hda with h | h
          · exact hq2 c b h
          · exact Cl_closed c b h q hq1
        · simp
  intro a b hab q hq
  have hk := key hq
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hk
  exact hk.2 a b hab
end Formalism.FourierDecayAlt.P.ClosureOperators
