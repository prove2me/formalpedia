-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.triple_form_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:00.015804+00:00
-- url     : https://prove2.me/submissions/13e7df0b-8172-4dfb-a09d-4d3896543484

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_dualSpan
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamN_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamN_latZ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x2 Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.TTStep := by
  have hD := dualSpan
  intro K _ R ψ hsd n Z Z' hZ hZ' hfin φ k hk hT
  constructor
  · intro h v v' hv hker
    obtain ⟨a, ha⟩ := h k le_rfl hk
    rw [ha v v' hv]
    have : ∑ l ∈ Finset.Ioo k n, a l • lamN R Z l v = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [hker l (Finset.mem_Ioo.1 hl).1, smul_zero]
    rw [this, add_zero]
  · intro h j hkj hjn
    by_cases hjk : j = k
    swap
    · exact hT j (by omega) hjn
    subst hjk
    let lamC : ℕ → coker R Z →ₗ[R] KR R :=
      fun l => (latZ R Z).liftQ (lamN R Z l) (lamN_latZ R Z hZ l)
    let lamC' : coker R Z' →ₗ[R] KR R := (latZ R Z').liftQ (lamN R Z' j) (lamN_latZ R Z' hZ' j)
    let μ : coker R Z →ₗ[R] KR R := lamC'.comp φ.toLinearMap - lamC j
    have hμ := hD K R ψ hsd (coker R Z) {l // l ∈ Finset.Ioo j n} (fun l => lamC l.1) μ (by
      intro c hc
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
      have := h v v' hv'.symm (by
        intro l hl
        by_cases hln : l < n
        · exact hc ⟨l, Finset.mem_Ioo.2 ⟨hl, hln⟩⟩
        · rw [lamN_big R Z l (by omega)]; rfl)
      show lamC' (φ (Submodule.Quotient.mk v)) - lamC j (Submodule.Quotient.mk v) = 0
      rw [← hv']
      show lamN R Z' j v' - lamN R Z j v = 0
      rw [this, sub_self])
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hμ
    classical
    refine ⟨fun l => if hl : l ∈ Finset.Ioo j n then cf ⟨l, hl⟩ else 0, ?_⟩
    intro v v' hv
    have e1 := congrArg (fun f : coker R Z →ₗ[R] KR R => f (Submodule.Quotient.mk v)) hcf
    simp only [LinearMap.sum_apply, LinearMap.smul_apply] at e1
    have e2 : μ (Submodule.Quotient.mk v) = lamN R Z' j v' - lamN R Z j v := by
      show lamC' (φ (Submodule.Quotient.mk v)) - lamC j (Submodule.Quotient.mk v) = _
      rw [hv]; rfl
    rw [e2] at e1
    rw [← Finset.sum_attach]
    have e3 : ∑ x ∈ (Finset.Ioo j n).attach,
        (if hl : x.1 ∈ Finset.Ioo j n then cf ⟨x.1, hl⟩ else 0) • lamN R Z x.1 v =
        ∑ x : {l // l ∈ Finset.Ioo j n}, cf x • lamC x.1 (Submodule.Quotient.mk v) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [dif_pos x.2]; rfl
    rw [e3, e1]; abel
end Formalism.FourierDecayAlt.P
