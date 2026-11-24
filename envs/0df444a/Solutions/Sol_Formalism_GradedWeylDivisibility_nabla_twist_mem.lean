-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nabla_twist_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:59.576172+00:00
-- url     : https://prove2.me/submissions/a4b9fba8-d622-49aa-87ae-2b2253f95247

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLTwMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : NablaLTwMem := by
  intro R K _ _ _ m lam g hg F
  have hd : g.det ≠ 0 := hg.ne_zero
  unfold nablaLTw nablaL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨G, hG, rfl⟩
    rw [Submodule.mem_comap] at hG
    change g.det ^ lam (Fin.last m) • rowAct K g (g.det ^ (-(lam (Fin.last m))) • G) ∈ _
    rw [map_smul, smul_smul, ← zpow_add₀ hd, add_neg_cancel, zpow_zero, one_smul]
    exact hG
  · intro hF
    refine ⟨g.det ^ (lam (Fin.last m)) • F, ?_, ?_⟩
    · rw [Submodule.mem_comap]
      change rowAct K g (g.det ^ (lam (Fin.last m)) • F) ∈ _
      rw [map_smul]
      exact hF
    · change g.det ^ (-(lam (Fin.last m))) • g.det ^ (lam (Fin.last m)) • F = F
      rw [smul_smul, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_smul]
end Formalism.GradedWeylDivisibility
