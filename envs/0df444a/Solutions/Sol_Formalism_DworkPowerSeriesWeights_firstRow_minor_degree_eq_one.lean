-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.firstRow_minor_degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:26.633673+00:00
-- url     : https://prove2.me/submissions/37a1d0d6-13fd-4283-aaa3-58d7c814da38

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
theorem _root_.solution {R : Type u} [CommRing R] {m N1 p : ℕ} (hp1 : 1 ≤ p) (hpm : p ≤ m)
    (I : Fin p → Fin N1) (mono : Fin m × Fin N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      (∑ j, C ((1 : Matrix (Fin m) (Fin m) R) ⟨r.val, lt_of_lt_of_le r.isLt hpm⟩ j) * X (j, I r') :
        MvPolynomial (Fin m × Fin N1) R)).det.support) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin m × Fin N1 => y.1.val = 0), mono y) = 1 := by
  classical
  obtain ⟨τ, hτ, ⟨π, hπ⟩, rfl⟩ := shape_minor_mem _ I mono hm
  rw [count_pred τ I (fun j => j.val = 0)]
  have hv : ∀ i, (τ i).val = (π i).val := by
    intro i
    have := hπ i
    beta_reduce at this
    rw [Matrix.one_apply] at this
    by_contra hne
    apply this
    rw [if_neg]
    intro h
    exact hne (by rw [← h])
  refine Finset.card_eq_one.mpr ⟨π.symm ⟨0, hp1⟩, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hv]
  constructor
  · intro h
    rw [Equiv.eq_symm_apply]
    exact Fin.ext h
  · intro h
    rw [h, Equiv.apply_symm_apply]
end Formalism.DworkPowerSeriesWeights
