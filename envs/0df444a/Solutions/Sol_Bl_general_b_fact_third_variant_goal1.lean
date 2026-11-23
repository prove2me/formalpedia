-- Prove2me | solution 1 for Bl.general_b_fact_third_variant.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:03.791775+00:00
-- url     : https://prove2.me/submissions/713434cf-2dac-4644-855c-88c241496aeb

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_variant
namespace Bl.general_b_fact_third_variant
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] {Ψ : Finset.{0} (RingHom.{0, 0} E Complex)},
  (∀ (σ : RingHom.{0, 0} E Complex),
      Iff (Membership.mem.{0, 0} Ψ σ) (Not (Membership.mem.{0, 0} Ψ (NumberField.ComplexEmbedding.conjugate.{0} σ)))) →
    ∀ (x : Module.Free.ChooseBasisIndex.{0, 0} Int (NumberField.RingOfIntegers.{0} E) → Real),
      (∀ (τ : RingHom.{0, 0} E Complex),
          Membership.mem.{0, 0} Ψ τ →
            Eq.{1}
              (Finset.sum.{0, 0} Finset.univ.{0}
                fun (k : Module.Free.ChooseBasisIndex.{0, 0} Int (NumberField.RingOfIntegers.{0} E)) ↦
                HMul.hMul.{0, 0, 0} (Complex.ofReal (x k))
                  (DFunLike.coe.{1, 1, 1} τ
                    (NumberField.RingOfIntegers.val.{0}
                      (DFunLike.coe.{1, 1, 1} (NumberField.RingOfIntegers.basis.{0} E) k))))
              0) →
        Eq.{1} x 0 := by
  intro E _ _ Ψ hΨ x hx
  have hall : ∀ σ : RingHom E Complex, (Finset.univ.sum fun k =>
      (Complex.ofReal (x k)) * σ (NumberField.RingOfIntegers.val
        (NumberField.RingOfIntegers.basis E k))) = 0 := by
    intro σ
    by_cases hσ : σ ∈ Ψ
    · exact hx σ hσ
    · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ Ψ := by
        by_contra hc
        exact hσ ((hΨ σ).mpr hc)
      have h2 := congrArg (starRingEnd Complex) (hx _ hc)
      rw [map_sum, map_zero] at h2
      simpa only [map_mul, Complex.conj_ofReal, NumberField.ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_conj] using h2
  have hli := (NumberField.canonicalEmbedding.latticeBasis E).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  funext k
  have h3 := hli (fun k => Complex.ofReal (x k)) (by
    funext σ
    rw [Finset.sum_apply]
    simp only [NumberField.canonicalEmbedding.latticeBasis_apply, Pi.smul_apply,
      NumberField.canonicalEmbedding.apply_at, NumberField.integralBasis_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hall σ) k
  exact_mod_cast h3
end Bl.general_b_fact_third_variant
