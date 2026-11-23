-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.nak
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:24.426253+00:00
-- url     : https://prove2.me/submissions/44113c3a-004d-4ae9-986f-b609fb5cd1d4

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_unit_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace Adic
theorem _root_.solution (h : Adic R ϖ) {ι : Type} [Finite ι] (d : ι → K) (Λ : Submodule R K)
    (hd : ∀ Λ' : Submodule R K, (∀ i, d i ∈ Λ') → ∀ i, ∃ l ∈ Λ, ∃ l' ∈ Λ', d i = l + (ϖ : K) * l') :
    ∀ i, d i ∈ Λ := by
  have hfg : (Submodule.span R (Set.range d)).FG := Submodule.fg_span (Set.finite_range d)
  have hJ : Ideal.span {(⟨(ϖ : K), h.mem⟩ : R)} ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Ideal.mem_jacobson_bot.2 fun y => ?_
    obtain ⟨v, hv, e⟩ := h.unit_one ((ϖ : K) * (y : K)) ⟨y, y.2, rfl⟩
    refine IsUnit.of_mul_eq_one (⟨v, hv⟩ : R) (Subtype.ext ?_)
    show ((ϖ : K) * (y : K) + 1) * v = 1
    linear_combination e
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot (N := Λ) hfg hJ (by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨l, hl, l', hl', e⟩ := hd (Submodule.span R (Set.range d)) (fun i => Submodule.subset_span ⟨i, rfl⟩) i
    show d i ∈ _
    rw [e]
    exact Submodule.add_mem_sup hl
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl'))
  exact fun i => hle (Submodule.subset_span ⟨i, rfl⟩)
end Adic
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
