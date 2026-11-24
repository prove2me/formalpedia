-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.rc_idem_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:39.677664+00:00
-- url     : https://prove2.me/submissions/cf926980-8555-43f2-883d-fb4e6286c809

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (f t : E ⊗[F] v.adicCompletion F)
    (c : v.adicCompletion F) (hc : Valued.v c < 1) (hf : f * f = f)
    (hft : f = ((1 : E) ⊗ₜ[F] c) * t)
    (ht : letI := rcIntAlg (E := E) v; IsIntegral (v.adicCompletionIntegers F) t) : f = 0 := by
  letI := rcIntAlg (E := E) v
  obtain ⟨p, hpm, hp⟩ := ht
  have hc1 : Valued.v c ≤ 1 := le_of_lt hc
  obtain ⟨c', hc'⟩ : ∃ c' : v.adicCompletionIntegers F, (c' : v.adicCompletion F) = c :=
    ⟨⟨c, by
      first
      | exact hc1
      | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hc1
      | simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hc1⟩, rfl⟩
  subst hc'
  have hC : algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) c' =
      (1 : E) ⊗ₜ[F] (c' : v.adicCompletion F) := rfl

  have hq0 : (p.scaleRoots c').eval₂ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)) f = 0 := by
    rw [hft, ← hC, Polynomial.scaleRoots_eval₂_mul, hp, mul_zero]
  have hidem : ∀ i : ℕ, f * f ^ i = f := fun i => by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq i hf

  have key : f * algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) ((p.scaleRoots c').eval 1) = 0 := by
    have h := congrArg (f * ·) hq0
    simp only [mul_zero] at h
    rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum] at h
    rw [Polynomial.eval_eq_sum_range, map_sum, Finset.mul_sum, ← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_pow, mul_one, mul_left_comm, hidem, mul_comm]
  have hsplit : (p.scaleRoots c').eval 1 =
      (∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i)) + 1 := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.natDegree_scaleRoots, Finset.sum_range_succ]
    simp [Polynomial.coeff_scaleRoots, hpm.coeff_natDegree]

  have hlt : Valued.v ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
      v.adicCompletionIntegers F) : v.adicCompletion F) < 1 := by
    push_cast
    refine Valuation.map_sum_lt _ one_ne_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have h1 : Valued.v ((p.coeff i : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 := by
      first
      | exact (p.coeff i).2
      | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (p.coeff i).2
    have hm : p.natDegree - i = (p.natDegree - i - 1) + 1 := by omega
    rw [Valuation.map_mul, Valuation.map_pow, hm, pow_succ]
    calc Valued.v ((p.coeff i : v.adicCompletionIntegers F) : v.adicCompletion F) *
          (Valued.v (c' : v.adicCompletion F) ^ (p.natDegree - i - 1) * Valued.v (c' : v.adicCompletion F))
        ≤ 1 * (1 * Valued.v (c' : v.adicCompletion F)) :=
          mul_le_mul' h1 (mul_le_mul' (pow_le_one' hc1 _) le_rfl)
      _ < 1 := by rw [one_mul, one_mul]; exact hc
  have hU : (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    rw [hsplit]
    intro h0
    have h0' : ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
        v.adicCompletionIntegers F) : v.adicCompletion F) = -1 := by
      have : ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
          v.adicCompletionIntegers F) : v.adicCompletion F) + 1 = 0 := by
        rw [← h0]; push_cast; ring
      exact eq_neg_of_add_eq_zero_left this
    have hv := hlt
    rw [h0', Valuation.map_neg, Valuation.map_one] at hv
    exact lt_irrefl _ hv
  have hunit : IsUnit (algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)
      (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F)) :=
    (Ne.isUnit hU).map _
  exact hunit.mul_left_eq_zero.mp key
end Formalism.L2.SG.Pf.SatGramLoc
