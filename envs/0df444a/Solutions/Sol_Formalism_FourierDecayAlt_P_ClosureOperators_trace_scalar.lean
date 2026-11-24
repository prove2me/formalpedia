-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.trace_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:53.410023+00:00
-- url     : https://prove2.me/submissions/d182606a-a117-4d92-8dbe-88650e4791b3

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_top_of_stab
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_trace_comm
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
theorem _root_.solution [FiniteDimensional ℂ V] {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E)
    (hI : Irr E) : ∃ ζ : ℂ, ∀ v : V, (∑ c, E c c) v = ζ • v := by
  haveI := hI.1
  obtain ⟨ζ, hζ⟩ := Module.End.exists_eigenvalue (∑ c, E c c)
  refine ⟨ζ, fun v => ?_⟩
  have hS : Stab E (LinearMap.ker ((∑ c, E c c) - ζ • 1)) := by
    intro a b w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have e := congrArg (fun g : Module.End ℂ V => g w) (trace_comm hE a b)
    simp only [Module.End.mul_apply] at e
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hw ⊢
    rw [e, sub_eq_zero.mp hw, map_smul, sub_self]
  obtain ⟨w, hw⟩ := hζ.exists_hasEigenvector
  have hmem : w ∈ LinearMap.ker ((∑ c, E c c) - ζ • 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact hw.apply_eq_smul
  have htop := top_of_stab hI _ hS w hmem hw.2
  have hv : v ∈ LinearMap.ker ((∑ c, E c c) - ζ • 1) := by rw [htop]; trivial
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv
  exact hv
end Formalism.FourierDecayAlt.P.ClosureOperators
