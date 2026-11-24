-- Prove2me | solution 1 for Formalism.HN.DualPolygon.ident_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:15.053311+00:00
-- url     : https://prove2.me/submissions/514fb2ee-9768-468d-b418-95a497816b07

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
namespace Formalism.HN.DualPolygon
theorem _root_.solution {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a)
      (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
    simp
  rw [hq] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  have hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hm := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hm
    rcases hm with rfl | hc
    · rfl
    · rw [← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp
end Formalism.HN.DualPolygon
