-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.root_of_unity_mod_t
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:23.969698+00:00
-- url     : https://prove2.me/submissions/42275b17-1dbb-4d67-a69a-9de29c9850f0

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : RootUnityModT := by
  intro E _ _ α T hT hw hex
  classical
  obtain ⟨β, hβ⟩ := hex
  by_contra hne
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hne
    rw [mul_zero, sub_eq_zero] at hβ
    exact hβ
  have hβE : (α : E) - 1 = (T : E) * (β : E) := by
    have h1 := congrArg (fun z : NumberField.RingOfIntegers E => (z : E)) hβ
    simpa using h1
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hwβ : ∀ w : NumberField.InfinitePlace E, w (β : E) < 1 := by
    intro w
    have e : ∀ x : E, w x = ‖w.embedding x‖ := fun x => (NumberField.InfinitePlace.norm_embedding_eq w x).symm
    have h1 := hw w
    rw [e] at h1
    have h3 : w.embedding ((α : E) - 1) = (T : ℂ) * w.embedding (β : E) := by
      rw [hβE, map_mul, map_natCast]
    have h4 : ‖w.embedding ((α : E) - 1)‖ ≤ 2 := by
      rw [map_sub, map_one]
      calc ‖w.embedding (α : E) - 1‖ ≤ ‖w.embedding (α : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [h1, norm_one]; norm_num
    rw [h3, norm_mul, Complex.norm_natCast] at h4
    rw [e]
    nlinarith [norm_nonneg (w.embedding (β : E))]
  have hprod := NumberField.InfinitePlace.prod_eq_abs_norm (β : E)
  have hlt : ∏ w : NumberField.InfinitePlace E, w (β : E) ^ w.mult < 1 := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)]
    have hA : w0 (β : E) ^ w0.mult < 1 :=
      pow_lt_one₀ (by positivity) (hwβ w0) (NumberField.InfinitePlace.mult_ne_zero)
    have hB : ∏ w ∈ Finset.univ.erase w0, w (β : E) ^ w.mult ≤ 1 :=
      Finset.prod_le_one (fun w _ => by positivity) (fun w _ => pow_le_one₀ (by positivity) (hwβ w).le)
    have hB0 : 0 ≤ ∏ w ∈ Finset.univ.erase w0, w (β : E) ^ w.mult :=
      Finset.prod_nonneg (fun w _ => by positivity)
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ w0 (β : E)) w0.mult]
  have hNz : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ0
  have hN : Algebra.norm ℚ (β : E) = ((Algebra.norm ℤ β : ℤ) : ℚ) := (Algebra.coe_norm_int β).symm
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ (β : E) : ℚ) : ℝ)| := by
    rw [hN]
    push_cast
    exact_mod_cast Int.one_le_abs hNz
  rw [hprod, Rat.cast_abs] at hlt
  linarith
end Formalism.SLP.GlobalBoundRefinements.P
