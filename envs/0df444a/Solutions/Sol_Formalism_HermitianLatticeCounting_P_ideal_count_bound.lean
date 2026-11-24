-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:27.052643+00:00
-- url     : https://prove2.me/submissions/b5b3f9c0-d2a6-4898-96d0-8789f944bfec

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_tuple_count
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_prime_norm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_index
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_val
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5a4_fiber_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
open UniqueFactorizationMonoid
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : IdealCountBound := by
  intro K _ _ X hX
  classical
  have hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset (fun I hI => Nat.le_floor hI.2)
  refine ⟨hfin, ?_⟩
  obtain ⟨ι, hι⟩ := s5a4_index K
  let τ : Ideal (𝓞 K) → (Fin (finrank ℚ K) → ℕ) := fun I i =>
    (((normalizedFactors I).filter (fun Q => ι Q = i)).map Ideal.absNorm).prod
  have hprod : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ∏ i, τ I i = Ideal.absNorm I := by
    intro I hI
    simp only [τ]
    rw [s5a4_fiber_prod ι (fun Q => Ideal.absNorm Q) (normalizedFactors I)]
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, map_multiset_prod]
  have hfac : ∀ I : Ideal (𝓞 K), ∀ Q ∈ normalizedFactors I, Q.IsPrime ∧ Q ≠ ⊥ := by
    intro I Q hQ
    have := prime_of_normalized_factor Q hQ
    exact ⟨Ideal.isPrime_of_prime this, this.ne_zero⟩
  have hinj : ∀ I J : Ideal (𝓞 K), I ≠ ⊥ → J ≠ ⊥ → τ I = τ J → I = J := by
    intro I J hI hJ h
    have : normalizedFactors I = normalizedFactors J := by
      ext P
      by_cases hP : P.IsPrime ∧ P ≠ ⊥
      · obtain ⟨p, k, hp, hk1, _, hpP, hk⟩ := s5a4_prime_norm P hP.1 hP.2
        have h1 := s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors I) (hfac I)
        have h2 := s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors J) (hfac J)
        have h3 : τ I (ι P) = τ J (ι P) := congrFun h _
        simp only [τ] at h3
        rw [h3, h2] at h1
        exact (Nat.eq_of_mul_eq_mul_left hk1 h1).symm
      · rw [Multiset.count_eq_zero_of_notMem (fun h => hP (hfac I P h)),
          Multiset.count_eq_zero_of_notMem (fun h => hP (hfac J P h))]
    rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ, this]
  have hcard : hfin.toFinset.card ≤ ((Fintype.piFinset (fun _ : Fin (finrank ℚ K) =>
      Finset.Icc 1 ⌊X⌋₊)).filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card := by
    apply Finset.card_le_card_of_injOn τ
    · intro I hI
      obtain ⟨hI0, hIX⟩ := hfin.mem_toFinset.mp hI
      have hN0 : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI0
      rw [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset, hprod I hI0]
      refine ⟨fun i => ?_, hIX⟩
      have hd : τ I i ∣ Ideal.absNorm I := by
        rw [← hprod I hI0]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_ne_zero (fun h0 => hN0 (by rw [h0] at hd; exact Nat.eq_zero_of_zero_dvd hd)),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd).trans (Nat.le_floor hIX)⟩
    · intro I hI J hJ h
      exact hinj I J (hfin.mem_toFinset.mp hI).1 (hfin.mem_toFinset.mp hJ).1 h
  rw [Set.ncard_eq_toFinset_card _ hfin]
  calc ((hfin.toFinset.card : ℕ) : ℝ) ≤ _ := by exact_mod_cast hcard
    _ ≤ _ := s5a4_tuple_count (finrank ℚ K) X hX
end Formalism.HermitianLatticeCounting.P
