-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.TT_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:13.610558+00:00
-- url     : https://prove2.me/submissions/8b18ccda-f7b4-43cc-94a6-a78eff0056f4

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff


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
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (Q : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hQ : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k))) (a : ι → K) (ha : Q = ∑ b, a b • Ψ b) :
    D.TT j cc PP Q = ∑ b, a b • PP b := by
  classical
  have hQsupp : ∀ lam ∈ Q.support, ∀ k, ldeg lam k = D.dO (D.eA j k) := by
    intro lam hlam k
    exact (mem_PolK_iff _ Q).mp hQ lam hlam k
  set c : ι → K := fun b => ∑ lam ∈ Q.support, Q.coeff lam * cc lam b with hc
  have hT : D.TT j cc PP Q = ∑ b, c b • PP b := by
    simp only [TT, lsup_apply, Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
    exact Finset.sum_comm
  have hQ' : Q = ∑ b, c b • Ψ b := by
    calc Q = ∑ lam ∈ Q.support, Q.coeff lam • monomial lam (1 : K) := by
            conv_lhs => rw [Q.as_sum]
            refine Finset.sum_congr rfl fun lam _ => ?_
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      _ = ∑ lam ∈ Q.support, Q.coeff lam • ∑ b, cc lam b • Ψ b := by
            refine Finset.sum_congr rfl fun lam hlam => ?_
            rw [hcc lam (hQsupp lam hlam)]
      _ = ∑ b, c b • Ψ b := by
            simp only [Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
            exact Finset.sum_comm
  have hca : ∀ b, c b = a b := by
    have h0 : ∑ b, (c b - a b) • Ψ b = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hQ', ← ha, sub_self]
    intro b
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 b)
  rw [hT]
  exact Finset.sum_congr rfl fun b _ => by rw [hca b]
end Formalism.MainNotions.PlaneGram.TwistData
