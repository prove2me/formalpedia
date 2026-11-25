-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.EZ_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:06.913848+00:00
-- url     : https://prove2.me/submissions/5c58e166-14ee-43f2-a2cd-5d7e7150e186

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_inLie_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_antihermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hpart1_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hpart2_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_dec
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_fun_add
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_sub__0af415330cc5
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_RdV
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (Z W : Mat k r) (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) :
    EZ Z (EZ W Φ) g - EZ W (EZ Z Φ) g = EZ (Z * W - W * Z) Φ g := by
  set Z1 := hpart1 (Hpk k r) Z
  set Z2 := hpart2 (Hpk k r) Z
  set W1 := hpart1 (Hpk k r) W
  set W2 := hpart2 (Hpk k r) W
  have hZ1 : inLie k r Z1 := hermitian_part_mem_lie Z
  have hZ2 : inLie k r Z2 := antihermitian_part_mem_lie Z
  have hW1 : inLie k r W1 := hermitian_part_mem_lie W
  have hW2 : inLie k r W2 := antihermitian_part_mem_lie W
  have hl1 : Loc 1 Φ g := loc_mono (by norm_num) hloc
  have hl2 : ∀ X, inLie k r X → Loc 1 (RdV X Φ) g := fun X hX => loc_RdV hX (loc_mono (by norm_num) hloc)
  have eW : EZ W Φ = fun x => RdV W1 Φ x + Complex.I • RdV W2 Φ x := rfl
  have eZ : EZ Z Φ = fun x => RdV Z1 Φ x + Complex.I • RdV Z2 Φ x := rfl
  have L : ∀ X Y Y', inLie k r X → inLie k r Y → inLie k r Y' →
      RdV X (fun x => RdV Y Φ x + Complex.I • RdV Y' Φ x) g =
        RdV X (RdV Y Φ) g + Complex.I • RdV X (RdV Y' Φ) g :=
    fun X Y Y' hX hY hY' => rdV_fun_add (hl2 Y hY) (hl2 Y' hY') hgG hX Complex.I
  have hPQ : Z * W - W * Z = ((Z1 * W1 - W1 * Z1) - (Z2 * W2 - W2 * Z2)) +
      Complex.I • ((Z1 * W2 - W2 * Z1) + (Z2 * W1 - W1 * Z2)) := by
    conv_lhs => rw [dec Z, dec W]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, smul_add, smul_sub]
    module
  have hP : inLie k r ((Z1 * W1 - W1 * Z1) - (Z2 * W2 - W2 * Z2)) :=
    B4.inLie_sub (inLie_comm hZ1 hW1) (inLie_comm hZ2 hW2)
  have hQ : inLie k r ((Z1 * W2 - W2 * Z1) + (Z2 * W1 - W1 * Z2)) :=
    B4.inLie_add (inLie_comm hZ1 hW2) (inLie_comm hZ2 hW1)
  have hR : EZ (Z * W - W * Z) Φ g =
      RdV ((Z1 * W1 - W1 * Z1) - (Z2 * W2 - W2 * Z2)) Φ g +
        Complex.I • RdV ((Z1 * W2 - W2 * Z1) + (Z2 * W1 - W1 * Z2)) Φ g := by
    unfold EZ; rw [hPQ, hpart1_dec hP hQ, hpart2_dec hP hQ]
  rw [hR, rdV_sub' hl1 hgG (inLie_comm hZ1 hW1) (inLie_comm hZ2 hW2),
    rdV_add hl1 hgG (inLie_comm hZ1 hW2) (inLie_comm hZ2 hW1),
    ← rdV_comm hloc hgG hZ1 hW1, ← rdV_comm hloc hgG hZ2 hW2, ← rdV_comm hloc hgG hZ1 hW2,
    ← rdV_comm hloc hgG hZ2 hW1]
  show (RdV Z1 (EZ W Φ) g + Complex.I • RdV Z2 (EZ W Φ) g) -
    (RdV W1 (EZ Z Φ) g + Complex.I • RdV W2 (EZ Z Φ) g) = _
  rw [eW, eZ, L Z1 W1 W2 hZ1 hW1 hW2, L Z2 W1 W2 hZ2 hW1 hW2, L W1 Z1 Z2 hW1 hZ1 hZ2,
    L W2 Z1 Z2 hW2 hZ1 hZ2]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I]
  module
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
