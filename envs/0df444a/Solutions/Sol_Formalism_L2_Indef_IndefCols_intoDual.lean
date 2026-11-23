-- Prove2me | solution 1 for Formalism.L2.Indef.IndefCols.intoDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:12.22914+00:00
-- url     : https://prove2.me/submissions/4437b8df-c184-4b95-83c4-9eefdb34e1a5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_IndefRows_RR_spec
import Theorems.Thm_Formalism_L2_Indef_matLat_mul
import Theorems.Thm_Formalism_L2_Indef_matLat_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
namespace IndefCols
theorem _root_.solution (hD : DivIntoDualShift) (hG : LatticeGlue) {Bs : DefBase K} {Df : DefSide Bs}
    {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs} (wf : Df.WF) (S : IndefCols Df Dc Sp N) (u : Dc.Mem)
    (Nu Nu' : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
    (τ : HeightOneSpectrum (𝓞 K) → ℤ)
    (hL2 : ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df.Mt (S.μ w),
      Dc.Pt u (S.μ w) φ F = 0 ∨ σ w ≤ (vw w (Dc.Pt u (S.μ w) φ F) : ℝ))
    (hτ : ∀ w, τ w ≤ ⌈σ w⌉) (hsh : IsShift Nu Nu' τ) :
    ∀ φ ∈ Nu', S.col.B u φ ∈ Formalism.HN.dualLat S.RR := by
  intro φ hφ x hx
  refine hD K (Dc.a u) S.D S.RR (S.col.B u) (fun w => Df.nV (S.μ w)) (fun w => Df.Mt (S.μ w))
    (fun w => S.ι (S.μ w) * Df.Pq (S.μ w)) (fun _ => 1) (fun w => Dc.Pt u (S.μ w))
    (fun w => S.col.ζ u (S.μ w)) (fun w => S.l1b.2.2.1 u _) (fun w => S.l1b.2.2.2 u w)
    (fun w φ F => ?_) Nu Nu' σ τ hL2 hτ hsh (fun w => ?_) φ hφ x hx
  · rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    exact S.l1b.1 u _ φ F
  · rw [matLat_one, matLat_mul]
    exact (S.toIndefRows.RR_spec hG wf).2 w
end IndefCols
end Formalism.L2.Indef
