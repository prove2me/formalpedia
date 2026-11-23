-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.degree_plain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:45.002234+00:00
-- url     : https://prove2.me/submissions/2874f8cf-b80b-417f-9515-ab5caae3cd1e

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_sum
import Theorems.Thm_Formalism_LT_CoeffP_Bd_sum


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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OneGauss
namespace Formalism.DworkPowerSeriesWeights.OneGauss
theorem _root_.solution {K : Type} [Field K] {N0 N1 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (κ : Fin N0 × Fin N1 →₀ ℕ)
    (hκ : κ ∈ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I).support) :
    κ.degree = ∑ c, p c := by
  have hdet : ∀ c : Fin C, (Matrix.of fun (r r' : Fin (p c)) =>
      (MvPolynomial.X (⟨(r : ℕ), lt_of_lt_of_le r.2 (hp c)⟩, I c r') :
        MvPolynomial (Fin N0 × Fin N1) K)).det.IsHomogeneous (p c) := by
    intro c
    rw [Matrix.det_apply]
    apply MvPolynomial.IsHomogeneous.sum
    intro s _
    have hprod := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin (p c)))
      (fun i => (Matrix.of fun (r r' : Fin (p c)) =>
        (MvPolynomial.X (⟨(r : ℕ), lt_of_lt_of_le r.2 (hp c)⟩, I c r') :
          MvPolynomial (Fin N0 × Fin N1) K)) (s i) i) (fun _ => 1)
      (fun i _ => by simpa using MvPolynomial.isHomogeneous_X K _)
    have hsum : (∑ _i ∈ (Finset.univ : Finset (Fin (p c))), 1) = p c := by simp
    rw [hsum] at hprod
    rw [Units.smul_def, zsmul_eq_mul,
      ← map_intCast (MvPolynomial.C : K →+* MvPolynomial (Fin N0 × Fin N1) K)]
    exact hprod.C_mul _
  have hmin := MvPolynomial.IsHomogeneous.prod Finset.univ _ _ (fun c _ => hdet c)
  have h := hmin (MvPolynomial.mem_support_iff.mp hκ)
  rw [Finsupp.degree_eq_weight_one]
  exact h
end Formalism.DworkPowerSeriesWeights.OneGauss
