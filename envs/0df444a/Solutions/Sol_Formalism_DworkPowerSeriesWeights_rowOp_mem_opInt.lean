-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.rowOp_mem_opInt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:36.232052+00:00
-- url     : https://prove2.me/submissions/f211eb28-7a88-492b-952a-7eb286a76495

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowOp_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_opA_norm_le

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
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {d N0 N1 : ℕ}
    (TT : Finset (ZMod d)) (T : ZMod d → Fin N0 → Fin N0 → K) (hT : ∀ s i k, ‖T s i k‖ ≤ 1)
    (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    rowOp (N1 := N1) TT T s i b ∈ opInt K (ZV d N0 N1) := by
  classical
  rw [rowOp_eq]
  refine Subring.sum_mem _ fun k _ => ?_
  intro κ
  rw [coeff_C_mul, coeff_X, norm_mul]
  refine mul_le_one₀ (opA_norm_le TT T hT s i k) (norm_nonneg _) ?_
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
