-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_shifted_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.883122+00:00
-- url     : https://prove2.me/submissions/ffa0af03-1911-4d2e-873b-90e1a3bc1a49

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_succ_div_injective_int_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (n : ℕ) (μ : Fin n → ℝ) (s : Fin n) (hμ : Function.Injective μ)
    (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) (hinj : Function.Injective (μ + Pi.single s 1)) :
    1 / (n : ℝ) ≤ ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ∧
      ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ≤ n := by
  choose z hz using hint s
  have hcard : ((univ.erase s).card : ℝ) + 1 = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := Fin.pos s
    rw [Nat.cast_sub this, Nat.cast_one]
    ring
  have hz0 : ∀ s' ∈ univ.erase s, z s' ≠ 0 := by
    intro s' hs' h
    apply Finset.ne_of_mem_erase hs'
    apply hμ
    have := hz s'
    rw [h] at this
    push_cast at this
    linarith
  have hz1 : ∀ s' ∈ univ.erase s, z s' ≠ -1 := by
    intro s' hs' h
    have hne := Finset.ne_of_mem_erase hs'
    apply hne
    apply hinj
    have := hz s'
    rw [h] at this
    push_cast at this
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne]
    linarith
  have hzinj : Set.InjOn z ((univ.erase s : Finset (Fin n)) : Set (Fin n)) := by
    intro a _ b _ hab
    apply hμ
    have h1 := hz a
    have h2 := hz b
    rw [hab] at h1
    linarith
  have hc := prod_succ_div_injective_int_bounds (univ.erase s) z hzinj hz0 hz1
  have heq : ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') =
      ∏ s' ∈ univ.erase s, (((z s' : ℝ) + 1) / (z s' : ℝ)) := by
    refine Finset.prod_congr rfl (fun s' _ => ?_)
    rw [← hz s']
    ring
  rw [heq, ← hcard]
  exact hc
end Formalism.HermitianLatticeCounting.P
