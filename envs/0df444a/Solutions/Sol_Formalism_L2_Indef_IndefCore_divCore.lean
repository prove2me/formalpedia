-- Prove2me | solution 1 for Formalism.L2.Indef.IndefCore.divCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:41.432979+00:00
-- url     : https://prove2.me/submissions/45088fc7-4cf5-4fc9-9562-74d8650e7d04

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_IndefSide_boundsMu
import Theorems.Thm_Formalism_L2_Indef_IndefCols_height

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
namespace IndefCore
theorem _root_.solution [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) (hH : HeightBoundConstant) {Bs : DefBase K} {Df0 Df1 : DefSide Bs}
    {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs} [Nonempty Bs.Ix] (wf0 : Df0.WF) (wf1 : Df1.WF)
    (P : IndefCore Df0 Df1 Dc Sp N) (hde : 0 ≤ N.de) (hde3 : N.de ≤ 1 / 3)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df0.dQ t) → Fin (Df0.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df0.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : P.base.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y (Df0.Gm eb (P.base.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y (Df0.Gm eb (P.base.μ y) y) : ℝ) ≤ (P.base.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ P.base.Tw, ∀ j, (jw (Df0.HT j (P.base.μ y)) y (Df0.Tl j (P.base.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * N.J0 (P.base.μ y) y j) * (P.base.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ P.base.Tw, lw y * ηy y j / (P.base.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3)
    (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det) (hne : P.cols.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df1.nV Bs.μ0)) (Fin (Df1.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df1.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df1.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v)
    (X : ℝ)
    (hX : X = (∑ j, N.l3 j) + 2 * (∑ j, ∑ y ∈ P.base.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + LG +
      (∑ j, (N.E1 j + E2 j)) + E3) :
    P.cols.muCC + Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
        (Formalism.HN.dualFrame P.cols.XE) (P.cols.col.B u) ≤
      X + 3 * N.de * (X + N.hh + 28 * N.la) + 28 * N.la +
        ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j) := by
  have h0 : P.base.muCC ≤ _ :=
    P.base.boundsMu hM hS hR0 hG hRam wf0 P.extra.untw eb heb Sy hSy hG0 LG E3 E2 gy ηy hi hLG hiv hE2 hE3
  have hp := (P.extra.passage hde hde3 _ P.extra.fun0).2
  have hh := P.cols.height hH wf1 u hXc hne X0 hX0 pU hpU
  have hκ : meanLog P.cols.κ = meanLog P.base.κ := by rw [P.extra.level.2.1]
  rw [hκ] at hh
  have h1 : P.base.muCC - meanLog P.base.κ ≤ X := by rw [hX]; linarith [h0]
  have h2 : 3 * N.de * (P.base.muCC + (N.hh - meanLog P.base.κ) + 28 * N.la) ≤
      3 * N.de * (X + N.hh + 28 * N.la) :=
    mul_le_mul_of_nonneg_left (by linarith [h1]) (by linarith [hde])
  linarith [hp, hh, h1, h2]
end IndefCore
end Formalism.L2.Indef
