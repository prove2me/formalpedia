-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.firstRow_minor_degree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:27.307486+00:00
-- url     : https://prove2.me/submissions/9b5501e1-974e-4b98-9495-bdc9a27c822e

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_count_pred
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_minor_mem
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R : Type u} [CommRing R] {m N1 p : ℕ} (A : Fin p → Fin m → R)
    (I : Fin p → Fin N1) (mono : Fin m × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C (A r j) * X (j, I r') : MvPolynomial (Fin m × Fin N1) R)).det.support) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin m × Fin N1 => y.1.val = 0), mono y) ≤ 1 := by
  classical
  obtain ⟨τ, hτ, _, rfl⟩ := shape_minor_mem A I mono hm
  rw [count_pred τ I (fun j => j.val = 0)]
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hτ (Fin.ext (ha.trans hb.symm))
end Formalism.DworkPowerSeriesWeights
