-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.separated_sum_le_prod_integrals
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:26.391717+00:00
-- url     : https://prove2.me/submissions/16204a4f-b878-4cc7-890f-fc021018a8b1

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_polydisc_eq_pi_ball
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volume_real_E1polydisc_eq_pi_mul_sq_pow_card
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_measurableSet_E1polydisc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hd : SeparatedPolydiscsDisjoint) {ι : Type} [Fintype ι] (ro : ℝ) (S : Finset (ι → ℂ)) (hro : 0 < ro)
    (hS : IsNormSeparated ro S) (φ ψ : ι → ℂ → ℝ) (hψ : ∀ v z, 0 ≤ ψ v z)
    (hφ : ∀ v z, 0 ≤ φ v z)
    (hint : ∀ v, Integrable (ψ v)) (hcmp : ∀ v D x, ‖x - D‖ < ro / 2 → φ v D ≤ ψ v x) :
    (∑ D ∈ S, ∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι ≤ ∏ v, ∫ x, ψ v x := by
  have hF : Integrable (fun x : ι → ℂ => ∏ v, ψ v (x v)) := Integrable.fintype_prod hint
  rw [← integral_fintype_prod_volume_eq_prod (fun v => ψ v), Finset.sum_mul]
  calc ∑ D ∈ S, (∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι
      ≤ ∑ D ∈ S, ∫ x in CenteredPolydisc ro D, ∏ v, ψ v (x v) := by
        apply Finset.sum_le_sum
        intro D _
        have h1 : ∫ _x in CenteredPolydisc ro D, (∏ v, φ v (D v)) =
            (∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι := by
          rw [setIntegral_const, volume_real_E1polydisc_eq_pi_mul_sq_pow_card ro hro, smul_eq_mul, mul_comm]
        rw [← h1]
        apply setIntegral_mono_on _ hF.integrableOn (measurableSet_E1polydisc ro D)
        · intro x hx
          exact Finset.prod_le_prod (fun v _ => hφ v _) (fun v _ => hcmp v _ _ (hx v))
        · rw [integrableOn_const_iff]
          right
          have : (volume : Measure (ι → ℂ)) (CenteredPolydisc ro D) ≠ ⊤ := by
            rw [polydisc_eq_pi_ball, volume_pi_pi]
            exact ENNReal.prod_ne_top fun v _ => measure_ball_lt_top.ne
          exact this.lt_top
    _ = ∫ x in ⋃ D ∈ S, CenteredPolydisc ro D, ∏ v, ψ v (x v) := by
        rw [integral_biUnion_finset S (fun D _ => measurableSet_E1polydisc ro D) _ (fun D _ => hF.integrableOn)]
        intro D hD D' hD' hne
        exact hd ι ro D D' hro hne (hS D hD D' hD' hne)
    _ ≤ ∫ x : ι → ℂ, ∏ v, ψ v (x v) :=
        setIntegral_le_integral hF (Filter.Eventually.of_forall fun x =>
          Finset.prod_nonneg fun v _ => hψ v _)
end Formalism.HermitianLatticeCounting.P
