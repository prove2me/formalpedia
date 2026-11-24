-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.hom_divided_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:15.445699+00:00
-- url     : https://prove2.me/submissions/f8ec6b73-121f-467e-a48b-a8c4e23c884d

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_pow_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : HomDiv := by
  intro p _ V W ι _ _ _ _ _ EV EW L M hM hL hW
  unfold ZpClosed DivStable HomLat at *
  refine ⟨fun c hc φ hφ => ?_, fun a b hab k φ hφ => ?_⟩
  · have hφ' : ∀ y ∈ L, φ y ∈ M := hφ
    show ∀ y ∈ L, (c • φ) y ∈ M
    intro y hy
    exact hM c hc _ (hφ' y hy)
  · have hφ' : ∀ y ∈ L, φ y ∈ M := hφ
    show ∀ y ∈ L, ((k.factorial : Padic p)⁻¹ • (homAct EV EW a b ^ k) φ) y ∈ M
    intro x hx
    rw [LinearMap.smul_apply, homAct_pow_apply, Finset.smul_sum]
    refine AddSubgroup.sum_mem M fun m hm => ?_
    have hm' : m.1 + m.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hm
    have hx2 := hL a b hab m.2 x hx
    have hy := hW a b hab m.1 _ (hφ' _ hx2)
    have hn : ‖((-1 : Padic p) ^ m.2)‖ ≤ 1 := by simp
    have hz := hM _ hn _ hy
    simp only [map_smul, smul_smul] at hz
    simp only [smul_smul]
    convert hz using 2
    subst hm'
    have h1 : (m.1.factorial : Padic p) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (m.2.factorial : Padic p) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcn := Nat.add_choose_mul_factorial_mul_factorial m.2 m.1
    rw [add_comm m.2 m.1] at hcn
    have hc : ((m.1 + m.2).choose m.1 : Padic p) * m.2.factorial * m.1.factorial = (m.1 + m.2).factorial := by
      exact_mod_cast hcn
    rw [← hc]
    have h3 : ((m.1 + m.2).choose m.1 : Padic p) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right m.1 m.2)).ne'
    field_simp
end Formalism.InvariantFactorPaths.PW
