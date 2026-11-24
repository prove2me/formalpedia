-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.ec_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:34.136465+00:00
-- url     : https://prove2.me/submissions/572c14dd-8e5f-4cee-8414-bab126fc3002

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ElementaryGeneratorsLevelGroup
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_flow_of_lieL
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart_unique
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_lieL_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_lieL_bracket
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_lieL_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_bracket
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_comb
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_sub
import Theorems.Thm_Formalism_REAL_commutator_complex_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {i : Fin (r + 1)} {Z W : Mx k r} (hZ : Good k r i Z) (hW : Good k r i W)
    {f F : Mx k r → E} {U : Set (Mx k r)} (hL : LocExt (Glev k r i) f F U) {g : Mx k r}
    (hg : g ∈ U) (hgG : g ∈ Glev k r i) :
    Ec Z (Ec W f) g - Ec W (Ec Z f) g = Ec (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2⟩ := hZ
  obtain ⟨hY1, hY2⟩ := hW
  have hZW := commutator_complex_expand (hpart1 (Hpk k r) Z) (hpart2 (Hpk k r) Z) (hpart1 (Hpk k r) W)
    (hpart2 (Hpk k r) W)
  rw [← hpart_decomp Z, ← hpart_decomp W] at hZW
  have hP := lieL_sub (lieL_bracket hX1 hY1) (lieL_bracket hX2 hY2)
  have hQ := lieL_add (lieL_bracket hX1 hY2) (lieL_bracket hX2 hY1)
  obtain ⟨h1, h2⟩ := hpart_unique hP.1 hQ.1
  have eZ : Ec Z f = fun h => RdV (hpart1 (Hpk k r) Z) f h + Complex.I • RdV (hpart2 (Hpk k r) Z) f h :=
    rfl
  have eW : Ec W f = fun h => RdV (hpart1 (Hpk k r) W) f h + Complex.I • RdV (hpart2 (Hpk k r) W) f h :=
    rfl
  simp only [Ec]
  rw [eZ, eW]
  rw [loc_comb (flow_of_lieL hX1) (flow_of_lieL hY1) (flow_of_lieL hY2) hL hg hgG,
    loc_comb (flow_of_lieL hX2) (flow_of_lieL hY1) (flow_of_lieL hY2) hL hg hgG,
    loc_comb (flow_of_lieL hY1) (flow_of_lieL hX1) (flow_of_lieL hX2) hL hg hgG,
    loc_comb (flow_of_lieL hY2) (flow_of_lieL hX1) (flow_of_lieL hX2) hL hg hgG,
    hZW, h1, h2,
    loc_sub (flow_of_lieL (lieL_bracket hX1 hY1)) (flow_of_lieL (lieL_bracket hX2 hY2))
      (flow_of_lieL hP) hL hg hgG,
    loc_add (flow_of_lieL (lieL_bracket hX1 hY2)) (flow_of_lieL (lieL_bracket hX2 hY1))
      (flow_of_lieL hQ) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX1) (flow_of_lieL hY1) (flow_of_lieL (lieL_bracket hX1 hY1)) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX2) (flow_of_lieL hY2) (flow_of_lieL (lieL_bracket hX2 hY2)) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX1) (flow_of_lieL hY2) (flow_of_lieL (lieL_bracket hX1 hY2)) hL hg hgG,
    ← loc_bracket (flow_of_lieL hX2) (flow_of_lieL hY1) (flow_of_lieL (lieL_bracket hX2 hY1)) hL hg hgG]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  abel
end Formalism.FourierDecayAlt.Q.EabGlW
