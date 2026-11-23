-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.triple_form_end_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:47.999178+00:00
-- url     : https://prove2.me/submissions/01a04f4e-f32d-4ee8-9726-4df40ca66265

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_eLast
import Theorems.Thm_Formalism_FourierDecayAlt_P_inverse_last_column_formula
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
theorem _root_.solution : Formalism.FourierDecayAlt.A5.TTEnd := by
  have H := inverse_last_column_formula
  intro K _ R h h' s t t' hs h1 x y x' y' hx hy hx' hy' φ hφ hT
  have hn : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  have hn' : (addBlock h' s t').1.sum = h'.1.sum + s := by simp [addBlock]
  obtain ⟨a, ha⟩ := hT h.1.sum le_rfl (by omega)
  have e := ha (eLast R) (eLast R) hφ.1
  let c : Fin (addBlock h s t).1.sum := ⟨h.1.sum, by omega⟩
  let b : Fin (addBlock h s t).1.sum := ⟨h.1.sum + s - 1, by omega⟩
  let c' : Fin (addBlock h' s t').1.sum := ⟨h.1.sum, by omega⟩
  let b' : Fin (addBlock h' s t').1.sum := ⟨h.1.sum + s - 1, by omega⟩
  have hb : b.val + 1 = (addBlock h s t).1.sum := by simp only [b]; omega
  have hb' : b'.val + 1 = (addBlock h' s t').1.sum := by simp only [b']; omega
  have A := (H K h s t h1 x y hx hy c b c hb rfl).2.2
  have A' := (H K h' s t' h1 x' y' hx' hy' c' b' c' hb' hs).2.2
  have z : ∑ l ∈ Finset.Ioo h.1.sum (addBlock h s t).1.sum,
      a l • lamN R (x * pt (addBlock h s t).1 (addBlock h s t).2 * y) l (eLast R) = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Ioo] at hl
    have B := (H K h s t h1 x y hx hy ⟨l, hl.2⟩ b c hb rfl).2.1
      (by simpa [c, Fin.lt_def] using hl.1)
    have := lamTil_eLast R (x * pt (addBlock h s t).1 (addBlock h s t).2 * y) ⟨l, hl.2⟩ b hb
    simp only [lamN, LinearMap.comp_apply]
    rw [this, B]; simp
  rw [z, add_zero] at e
  have E := lamTil_eLast R (x * pt (addBlock h s t).1 (addBlock h s t).2 * y) c b hb
  have E' := lamTil_eLast R (x' * pt (addBlock h' s t').1 (addBlock h' s t').2 * y') c' b' hb'
  simp only [lamN, LinearMap.comp_apply] at e
  rw [show h.1.sum = c.val from rfl, E, A] at e
  rw [show c.val = c'.val from rfl, E', A'] at e
  have := (Submodule.Quotient.eq _).1 e.symm
  obtain ⟨r, hr⟩ := this
  rw [← hr]; exact r.2
end Formalism.FourierDecayAlt.P
