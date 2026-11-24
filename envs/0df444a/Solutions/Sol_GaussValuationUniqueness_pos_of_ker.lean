-- Prove2me | solution 1 for GaussValuationUniqueness.pos_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:24.989621+00:00
-- url     : https://prove2.me/submissions/8a627437-9cb3-4b74-a8d5-b62873506497

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Theorems.Thm_GaussValuationUniqueness_pos_of_not_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))
namespace GaussValuationUniqueness
theorem _root_.solution {w : AddValuation (OmS Ω D N) (WithTop ℤ)}
    (hw : ∀ a : Ω, w (algebraMap Ω (OmS Ω D N) a) = v a)
    (e : SVar D N → OmS Ω D N) (he : ∀ s, 0 ≤ w (e s))
    (q : MvPolynomial (SVar D N) (vRing v))
    (hq : MvPolynomial.map (IsLocalRing.residue (vRing v)) q = 0) :
    0 < w (MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) e q) := by
  rw [MvPolynomial.eval₂_eq]
  refine Finset.sum_induction _ (fun x => 0 < w x)
    (fun a b ha hb => lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add w a b)) (by simp) ?_
  intro d _
  have hprod : 0 ≤ w (∏ s ∈ d.support, e s ^ d s) :=
    Finset.prod_induction _ (fun x => 0 ≤ w x)
      (fun a b ha hb => by rw [AddValuation.map_mul]; exact add_nonneg ha hb)
      (le_of_eq (AddValuation.map_one w).symm)
      (fun s _ => by rw [AddValuation.map_pow]; exact nsmul_nonneg (he s) _)
  have hnu : ¬ IsUnit (q.coeff d) := by
    have h0 := congrArg (MvPolynomial.coeff d) hq
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h0
    exact (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)
  have hc : 0 < w (((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) (q.coeff d)) := by
    rw [RingHom.comp_apply, hw]
    exact pos_of_not_isUnit v _ hnu
  rw [AddValuation.map_mul]
  exact lt_of_lt_of_le hc (le_add_of_nonneg_right hprod)
end GaussValuationUniqueness
