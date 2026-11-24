-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.low_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:22.368042+00:00
-- url     : https://prove2.me/submissions/9962393c-9339-4d1b-ad2b-040d465b4cc3

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_firstRow_minor_degree_le_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoShapeLow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_prod_le
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
theorem _root_.solution {R : Type u} [CommRing R] {N0 N1 Cn : ℕ} (T : Fin N0 → Fin N0 → R)
    (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    ∀ mono ∈ (minorProd (oldRowLow (N1 := N1) T) p hp I).support,
      (∑ y, mono y) = ∑ c, p c ∧
      (∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) ≤ Cn := by
  intro mono hmono
  classical
  refine ⟨?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    exact (monoShapeLow R N0 N1 N0 Cn T p hp I mono hmono).1
  · unfold minorProd at hmono
    have := shape_prod_le (R := R) (fun mono : Fin N0 × Fin N1 →₀ ℕ =>
      ∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), mono y) (by simp)
      (fun a b => by simp [Finset.sum_add_distrib]) _
      (fun _ => 1) Finset.univ (fun c _ mono hm => firstRow_minor_degree_le_one (R := R) (N1 := N1)
        (fun (r : Fin (p c)) k => T ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ k) (I c) mono hm)
      mono hmono
    simpa using this
end Formalism.DworkPowerSeriesWeights
