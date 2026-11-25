-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.algIndep_of_der
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:44.006848+00:00
-- url     : https://prove2.me/submissions/deb88f1a-daad-45be-848e-688fbb798242

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_der_aeval
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_totalDegree_pderiv_lt
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_der_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_totalDegree_pderiv_lt
import Theorems.Thm_UpperTheory_Reformulated_B_Qf29_der_aeval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
variable {F : Type} [Field F]
namespace Formalism.L2.Pj.GenericSectionMinimum
theorem _root_.solution {E : Type} [Field E] [CharZero E] [Algebra E F] {N : ℕ} (t : Fin N → F)
    (δ : Fin N → F → F) (hδ : ∀ l, IsDer (δ l)) (hE : ∀ l e, δ l (algebraMap E F e) = 0)
    (ht : ∀ l k, δ l (t k) = if k = l then 1 else 0) : AlgebraicIndependent E t := by
  classical
  have main : ∀ n : ℕ, ∀ P : MvPolynomial (Fin N) E, P.totalDegree ≤ n →
      MvPolynomial.aeval t P = 0 → P = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih P hd hP
    have hder : ∀ l, MvPolynomial.pderiv l P = 0 := by
      intro l
      by_contra hne
      have hlt := totalDegree_pderiv_lt P l hne
      apply hne
      refine ih _ (lt_of_lt_of_le hlt hd) (MvPolynomial.pderiv l P) le_rfl ?_
      have hz := der_aeval (hδ l) (hE l) t P
      rw [hP, (hδ l).der_zero] at hz
      simpa [ht] using hz.symm
    have hdeg0 : P.totalDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro s hs
      by_contra hpos
      obtain ⟨l, hl⟩ : ∃ l, s l ≠ 0 := by
        by_contra hall
        push_neg at hall
        have h0 : s = 0 := Finsupp.ext fun a => by simp [hall a]
        simp [h0] at hpos
      have hs' : s - Finsupp.single l 1 + Finsupp.single l 1 = s := by
        ext j
        by_cases hj : j = l
        · subst hj
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same]
          omega
        · simp [Finsupp.single_apply, Ne.symm hj]
      have hc := MvPolynomial.coeff_pderiv (i := l) P (s - Finsupp.single l 1)
      rw [hder l, MvPolynomial.coeff_zero, hs'] at hc
      rw [MvPolynomial.mem_support_iff] at hs
      have h2 : (((s - Finsupp.single l 1 : Fin N →₀ ℕ) l : ℕ) : E) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
      exact hs ((mul_eq_zero.mp hc.symm).resolve_right h2)
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hdeg0
    rw [hdeg0, MvPolynomial.aeval_C] at hP
    have hc0 : MvPolynomial.coeff 0 P = 0 := (map_eq_zero (algebraMap E F)).mp hP
    rw [hdeg0, hc0, MvPolynomial.C_0]
  exact (injective_iff_map_eq_zero (MvPolynomial.aeval (R := E) t)).mpr fun P hP => main _ P le_rfl hP
end Formalism.L2.Pj.GenericSectionMinimum
