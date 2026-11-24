-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Th_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:25.211+00:00
-- url     : https://prove2.me/submissions/d32d99eb-8105-4415-8a52-1971af48cf61

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_C_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_hom_monomial
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lift_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_monomial_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twistMat_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {P : MvPolynomial (ι × Fin n) (GLLaurent R n)}
    (hP : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) :
    flt_Th LL S j P ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by
  have hone : ∀ s : ℤ, s = 0 → (1 : GLLaurent R n) ∈ (flt_L (GLCoord R n) e).F s := by
    rintro s rfl
    exact (flt_L (GLCoord R n) e).one_mem
  have hX : ∀ w, flt_Th LL S j (X w) ∈ (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F
      ((0 : (ι × Fin n →₀ ℕ) →+ ℤ) (Finsupp.single w 1)) := by
    intro w
    rw [AddMonoidHom.zero_apply]
    have hXw : (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 :=
      flt_monomial_mem (hone _ (by simp))
    simp only [flt_Th, eval₂Hom_X']
    refine AddSubgroup.add_mem _ (flt_C_mem hXw) ?_
    split_ifs with hS hv
    · refine AddSubgroup.sum_mem _ fun c _ => ?_
      rw [show (C (C (twistMat R n j (-1) c w.2)) * X (w.1, c) :
          MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n))) =
          monomial (Finsupp.single (w.1, c) 1) (C (twistMat R n j (-1) c w.2)) by
        rw [X, C_mul_monomial, mul_one]]
      refine flt_monomial_mem (flt_C_mem (flt_twistMat_mem R n j _ _ _ ?_ ?_ _ _)) <;>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [flt_cost, hS, hv]
    · refine AddSubgroup.sum_mem _ fun c _ => ?_
      rw [show (C (C (twistMat R n j 1 w.2 c)) * X (w.1, c) :
          MvPolynomial (ι × Fin n) (MvPolynomial (ι × Fin n) (GLLaurent R n))) =
          monomial (Finsupp.single (w.1, c) 1) (C (twistMat R n j 1 w.2 c)) by
        rw [X, C_mul_monomial, mul_one]]
      refine flt_monomial_mem (flt_C_mem (flt_twistMat_mem R n j _ _ _ ?_ ?_ _ _)) <;>
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [flt_cost, hS, hv]
    · have h1 : (1 : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F
          (0 - flt_cost LL S (!bm) (Finsupp.single w 1)) := by
        have h0 : flt_cost LL S (!bm) (Finsupp.single w 1) = 0 := by simp [flt_cost, hS]
        rw [h0, sub_zero]
        exact (laurentCoeffFiltration R n (ι × Fin n) e).one_mem
      exact flt_monomial_mem h1
  rw [P.as_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun m _ => ?_
  rw [show monomial m (coeff m P) = C (coeff m P) * monomial m 1 by rw [C_mul_monomial, mul_one], map_mul]
  have hc : coeff m P ∈ (flt_L (GLCoord R n) e).F t := by
    have h3 := (flt_lift_mem.1 hP) m
    simpa using h3
  have h1 : flt_Th LL S j (C (coeff m P)) ∈
      (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).F t := by
    simp only [flt_Th, eval₂Hom_C, RingHom.comp_apply]
    exact flt_C_mem (flt_C_mem hc)
  have h2 := flt_hom_monomial _ (flt_Th LL S j) 0 hX m
  rw [AddMonoidHom.zero_apply] at h2
  have h4 := (flt_lift (laurentCoeffFiltration R n (ι × Fin n) e) (flt_cost LL S (!bm))).mul_mem h1 h2
  rwa [add_zero] at h4
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
