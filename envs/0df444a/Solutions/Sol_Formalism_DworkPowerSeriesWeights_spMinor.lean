-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spMinor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:39.491159+00:00
-- url     : https://prove2.me/submissions/cccc8d6e-0447-477a-99d1-ee16022451fa

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spV_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_spEx_apply

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {m p : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (top : Fin (p + 1) → R) (A : Matrix (Fin (p + 1)) (Fin (p + 1))
      (MvPolynomial (Fin m × Fin (p + 1)) R)) (cf : Fin (p + 1) → Option (Fin m) → R)
    (hA : ∀ i c, A i c = ∑ o, MvPolynomial.C (cf i o) * spV top o c) :
    ∀ mono ∈ A.det.support, ∀ k : Fin m, (∑ c : Fin (p + 1), mono (k, c)) ≤ 1 := by
  classical
  have hrow : A = fun i => ∑ o,
      (MvPolynomial.C (cf i o) : MvPolynomial (Fin m × Fin (p + 1)) R) • spV top o := by
    funext i c
    rw [hA]
    simp [Finset.sum_apply, smul_eq_mul]
  have hdet : A.det = ∑ r : Fin (p + 1) → Option (Fin m),
      (∏ i, (MvPolynomial.C (cf i (r i)) : MvPolynomial (Fin m × Fin (p + 1)) R)) •
        (Matrix.of fun i => spV top (r i)).det := by
    rw [hrow]
    show Matrix.detRowAlternating (fun i => ∑ o,
      (MvPolynomial.C (cf i o) : MvPolynomial (Fin m × Fin (p + 1)) R) • spV top o) = _
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    rfl
  intro mono hmono k
  rw [hdet] at hmono
  obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmono)
  have hr' : mono ∈ (Matrix.of fun i => spV top (r i)).det.support := by
    rw [← map_prod, smul_eq_mul, MvPolynomial.C_mul'] at hr
    exact MvPolynomial.support_smul hr
  by_cases hinj : Function.Injective r
  · rw [Matrix.det_apply] at hr'
    obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hr')
    have hs' : mono ∈ (∏ c, (Matrix.of fun i => spV top (r i)) (s c) c).support := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
      · rwa [h, one_smul] at hs
      · rwa [h, Units.neg_smul, one_smul, MvPolynomial.support_neg] at hs
    simp only [Matrix.of_apply, spV_eq, ← MvPolynomial.monomial_sum_prod] at hs'
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs')
    subst he
    have hval : ∀ c, (∑ c', spEx (r (s c')) c') (k, c) = if r (s c) = some k then 1 else 0 := by
      intro c
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
      · rw [spEx_apply]; simp
      · intro c' _ hc'
        rw [spEx_apply]; simp [hc']
      · simp
    simp only [hval]
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact s.injective (hinj (ha.trans hb.symm))
  · exfalso
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i1, i2, h12, hne⟩ := hinj
    have h0 : (Matrix.of fun i => spV top (r i)).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by show spV top (r i1) = spV top (r i2); rw [h12])
    rw [h0] at hr'
    simp at hr'
end Formalism.DworkPowerSeriesWeights
