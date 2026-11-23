-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.op_minorProd_shape
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:34.545978+00:00
-- url     : https://prove2.me/submissions/e9d52863-9fae-4532-af15-28d36ae85ba5

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowDeg_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowDeg_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_minor_shape
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_prod_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_prod_le
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
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
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 Cn : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (mono : ZV d N0 N1 →₀ ℕ)
    (hm : mono ∈ (minorProd (rowOp (N1 := N1) TT T s) p hp I).support) :
    (∀ s' k, s' ≠ s → rowDeg s' k mono = 0) ∧ (∑ k, rowDeg s k mono) = ∑ c, p c ∧
      (∀ k, rowDeg s k mono ≤ Cn) ∧
      (s ∈ TT → (∀ c, 1 ≤ p c) → ∀ k0 : Fin N0, k0.val = 0 → rowDeg s k0 mono = Cn ∧
        ∀ k : Fin N0, k.val ≠ 0 →
          rowDeg s k mono ≤ (Finset.univ.filter (fun c => 2 ≤ p c)).card) := by
  classical
  unfold minorProd at hm
  have hmin := fun c => op_minor_shape TT T s (hp c) (I c)
  refine ⟨fun s' k hs => ?_, ?_, fun k => ?_, fun hs hp1 k0 hk0 => ⟨?_, fun k hk => ?_⟩⟩
  · have := shape_prod_eq (R := K) (rowDeg s' k) (rowDeg_zero _ _) (rowDeg_add _ _) _
      (fun _ => 0) Finset.univ (fun c _ m hm => (hmin c m hm).1 s' k hs) mono hm
    simpa using this
  · exact shape_prod_eq (R := K) (fun m => ∑ k, rowDeg s k m) (by simp [rowDeg_zero])
      (fun a b => by simp [rowDeg_add, Finset.sum_add_distrib]) _
      (fun c => p c) Finset.univ (fun c _ m hm => (hmin c m hm).2.1) mono hm
  · have := shape_prod_le (R := K) (rowDeg s k) (rowDeg_zero _ _) (rowDeg_add _ _) _
      (fun _ => 1) Finset.univ (fun c _ m hm => (hmin c m hm).2.2.1 k) mono hm
    simpa using this
  · have := shape_prod_eq (R := K) (rowDeg s k0) (rowDeg_zero _ _) (rowDeg_add _ _) _
      (fun _ => 1) Finset.univ (fun c _ m hm => ((hmin c m hm).2.2.2 hs (hp1 c) k0 hk0).1) mono hm
    simpa using this
  · have := shape_prod_le (R := K) (rowDeg s k) (rowDeg_zero _ _) (rowDeg_add _ _) _
      (fun c => if 2 ≤ p c then 1 else 0) Finset.univ
      (fun c _ m hm => ((hmin c m hm).2.2.2 hs (hp1 c) k0 hk0).2 k hk) mono hm
    rw [Finset.card_filter]
    exact this
end Formalism.DworkPowerSeriesWeights
