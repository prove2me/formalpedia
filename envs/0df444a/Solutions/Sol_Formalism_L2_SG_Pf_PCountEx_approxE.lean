-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.approxE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:38.959586+00:00
-- url     : https://prove2.me/submissions/cba806bd-4916-48ca-a2e8-a8c49335bb5c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SimpLemmas
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_approxF
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_iotaE_mem_O
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_alg_mem_O
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_exists_int_span
import Theorems.Thm_UpperTheory_Reformulated_B_ApproximationIntegralOutsideFinset_approxF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0) (a : ∀ p, (A p).Ep) :
    ∃ x : E, (∀ p ∈ S, ∃ o ∈ (A p).O,
        (A p).ιE x - a p = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, (A p).ιE x ∈ (A p).O := by
  obtain ⟨n, e, he⟩ := exists_int_span (F := F) (E := E)

  have hco : ∀ p, ∃ l : Fin n → (A p).Fp, ∑ j, l j • (A p).ιE (e j : E) = a p := by
    intro p
    have hsp : Submodule.span (A p).Fp (Set.range fun j => (A p).ιE (e j : E)) = ⊤ := by
      rw [eq_top_iff, ← (A p).span, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span F (Set.range fun j => (e j : E)) := by rw [he]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨j, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul t y _ hy =>
        rw [Algebra.smul_def, map_mul, (A p).compat, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hy
    have ha : a p ∈ Submodule.span (A p).Fp (Set.range fun j => (A p).ιE (e j : E)) := by rw [hsp]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun _).1 ha
  choose l hl using hco

  have hf := fun j : Fin n => approxF A S c hc (fun p => l p j)
  choose f hfS hfO using hf
  refine ⟨∑ j, algebraMap F E (f j) * (e j : E), fun p hp => ?_, fun q hq => ?_⟩
  · haveI := (A p).lf
    have hcF : (A p).ιF (algebraMap (𝓞 F) F c) ≠ 0 := by
      rw [map_ne_zero_iff _ (A p).ιF.injective, Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
      exact hc
    have hv0 : valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c)) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hcF
    refine ⟨∑ j, algebraMap (A p).Fp (A p).Ep
        (((A p).ιF (f j) - l p j) / (A p).ιF (algebraMap (𝓞 F) F c)) * (A p).ιE (e j : E), ?_, ?_⟩
    · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ (alg_mem_O A p ?_) (iotaE_mem_O A p (e j))
      rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 hv0)]
      exact hfS j p hp
    · rw [← hl p, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, (A p).compat, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hcF, ← sub_mul,
        map_sub]
  · haveI := (A q).lf
    rw [map_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [map_mul, (A q).compat]
    exact Subring.mul_mem _ (alg_mem_O A q (hfO j q hq)) (iotaE_mem_O A q (e j))
end Formalism.L2.SG.Pf.PCountEx
