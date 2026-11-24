-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.depth_valuation_sum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:19.13403+00:00
-- url     : https://prove2.me/submissions/5541c0af-8c23-46cb-9b68-ed2ca7fa34ce

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_mem_label_interval_of_mu_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_padicValInt_prod_eq_sum
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_padicValInt_pow_eq_mul
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_mu_w
import Theorems.Thm_Formalism_CohomologicalDescent_LD_muSupport
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution : DnValSum := by
  intro l k j t w M i lam xm xp hl hR
  have : Fact l.Prime := ⟨hl⟩
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  have hdw : ∀ b, dual M lam b ≤ M - w := fun b => by
    have := hb (Fin.rev b)
    unfold dual
    omega
  have hcont : ∀ c : ℤ, cont t w M (maxB t w + (((M - w : ℕ) : ℤ) - c)) = c := by
    intro c
    unfold cont
    ring
  unfold Dn
  have hne : ∀ x ∈ Finset.range (k + j + (M - w) + i),
      (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^
        mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0 := by
    intro x _
    by_cases h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0
    · have hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ) := by omega
      rw [hc, ld_mu_w]
      simp
    · exact pow_ne_zero _ h
  have hterm : ∀ x ∈ Finset.range (k + j + (M - w) + i),
      padicValInt l ((((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) ^
        mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ))) =
      mu t (M - w) i (dual M lam) ((x : ℤ) - ((k + j : ℕ) : ℤ)) *
        vl l (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) := by
    intro x _
    by_cases h : (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ))) = 0
    · have hc : ((x : ℤ) - ((k + j : ℕ) : ℤ)) = ((M - w : ℕ) : ℤ) := by omega
      rw [hc, ld_mu_w]
      simp
    · unfold vl
      exact padicValInt_pow_eq_mul l _ h _
  rw [padicValInt_prod_eq_sum l _ _ hne, Finset.sum_congr rfl hterm]
  refine Finset.sum_bij_ne_zero
    (fun x _ _ => maxB t w + (((M - w : ℕ) : ℤ) - ((x : ℤ) - ((k + j : ℕ) : ℤ)))) ?_ ?_ ?_ ?_
  · intro a _ h2
    have hmu : mu t (M - w) i (dual M lam) ((a : ℤ) - ((k + j : ℕ) : ℤ)) ≠ 0 := left_ne_zero_of_mul h2
    rw [← hcont ((a : ℤ) - ((k + j : ℕ) : ℤ))] at hmu
    exact Finset.mem_Ioo.mpr (mem_label_interval_of_mu_ne_zero k j t w M i lam xm xp hR _ hmu)
  · intro a1 _ _ a2 _ _ h
    omega
  · intro ct _ h2
    have hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0 := left_ne_zero_of_mul h2
    obtain ⟨h3, h4⟩ := muSupport t (M - w) i (k + j) (dual M lam) _ hdw hmu
    have ha : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) = cont t w M ct + ((k + j : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    have hx : (((cont t w M ct + ((k + j : ℕ) : ℤ)).toNat : ℕ) : ℤ) - ((k + j : ℕ) : ℤ) = cont t w M ct := by
      rw [ha]; ring
    have hv : ((M - w : ℕ) : ℤ) - cont t w M ct = ct - maxB t w := by
      unfold cont; ring
    refine ⟨(cont t w M ct + ((k + j : ℕ) : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · rw [hx, hv]
      exact h2
    · rw [hx, hv]
      ring
  · intro a _ _
    rw [hcont]
    congr 2
    ring
end Formalism.CohomologicalDescent.UnitNormBounds
