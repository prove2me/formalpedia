-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.820253+00:00
-- url     : https://prove2.me/submissions/df6d1d0f-e669-4ce6-9a25-a9f040913208

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_omega_mul_ge
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_max_above
import Theorems.Thm_Formalism_SLP_P_CountO_ncard_biUnion_le
import Theorems.Thm_Formalism_SLP_P_CountO_primes_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : IdealCountEq := by
  intro E _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  classical
  set N := Module.finrank ℚ E with hN
  have hNpos : 0 < N := Module.finrank_pos
  rcases Nat.eq_or_lt_of_le hn with h1 | h1
  · have : {I : Ideal (𝓞 E) | Ideal.absNorm I = 1} = {⊤} := by
      ext I; simp [Ideal.absNorm_eq_one_iff]
    rw [← h1, this]; simp
  · set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    obtain ⟨Ps, hPs, hPmem⟩ := Formalism.SLP.P.CountO.primes_card E p hp
    let G := Ps.filter (fun P => P.IsMaximal ∧ ((p : ℕ) : 𝓞 E) ∈ P)
    let t : Ideal (𝓞 E) → Set (Ideal (𝓞 E)) := fun P =>
      (fun I' => P * I') '' {I' | Ideal.absNorm P * Ideal.absNorm I' = n}
    have hsub : {I : Ideal (𝓞 E) | Ideal.absNorm I = n} ⊆ ⋃ P ∈ G, t P := by
      intro I hI
      have hI' : Ideal.absNorm I = n := hI
      obtain ⟨P, hP, hle, hpP⟩ := DualLatticeIndexBis.exists_max_above E I p hp (hI' ▸ hpn) (by omega)
      obtain ⟨I', rfl⟩ := Ideal.dvd_iff_le.mpr hle
      simp only [Set.mem_iUnion]
      refine ⟨P, Finset.mem_filter.mpr ⟨hPmem P hP hpP, hP, hpP⟩, I', ?_, rfl⟩
      rw [map_mul] at hI'
      exact hI'
    have hOm : 1 ≤ (Nat.primeFactorsList n).length := by
      have := DualLatticeIndexBis.omega_mul_ge (q := n) (n' := 1) h1 le_rfl
      rw [mul_one] at this
      omega
    have ht : ∀ P ∈ G, (t P).Finite ∧ (t P).ncard ≤ N ^ ((Nat.primeFactorsList n).length - 1) := by
      intro P hP
      obtain ⟨_, hPm, hpP⟩ := Finset.mem_filter.mp hP
      set q := Ideal.absNorm P with hq
      have hq0 : q ≠ 0 := by
        intro h
        rw [hq, Ideal.absNorm_eq_zero_iff] at h
        rw [h, Ideal.mem_bot] at hpP
        exact hp.ne_zero (by exact_mod_cast hpP)
      have hq1 : q ≠ 1 := by
        intro h
        rw [hq, Ideal.absNorm_eq_one_iff] at h
        exact hPm.ne_top h
      by_cases hqn : q ∣ n
      · obtain ⟨n', hn'⟩ := hqn
        have hn'1 : 1 ≤ n' := by
          rcases Nat.eq_zero_or_pos n' with h | h
          · rw [h, mul_zero] at hn'; omega
          · exact h
        have hlt : n' < n := by
          have hq2 : 2 ≤ q := by omega
          rw [hn']; nlinarith
        have hset : {I' : Ideal (𝓞 E) | q * Ideal.absNorm I' = n} =
            {I' : Ideal (𝓞 E) | Ideal.absNorm I' = n'} := by
          ext I'
          simp only [Set.mem_ofPred_eq]
          rw [hn']
          exact Nat.mul_right_inj hq0
        obtain ⟨hf, hc⟩ := ih n' hlt hn'1
        have hge := DualLatticeIndexBis.omega_mul_ge (q := q) (n' := n') (by omega) hn'1
        rw [← hn'] at hge
        simp only [t]
        rw [hset]
        refine ⟨hf.image _, (Set.ncard_image_le hf).trans (hc.trans ?_)⟩
        exact Nat.pow_le_pow_right hNpos (by omega)
      · have hset : {I' : Ideal (𝓞 E) | q * Ideal.absNorm I' = n} = ∅ := by
          ext I'
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          exact hqn ⟨_, h.symm⟩
        simp only [t]
        rw [hset]
        simp
    obtain ⟨hfin, hcard⟩ := Formalism.SLP.P.CountO.ncard_biUnion_le G t (fun P hP => (ht P hP).1)
    refine ⟨hfin.subset hsub, ?_⟩
    calc {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard ≤ (⋃ P ∈ G, t P).ncard :=
          Set.ncard_le_ncard hsub hfin
      _ ≤ ∑ P ∈ G, (t P).ncard := hcard
      _ ≤ ∑ _P ∈ G, N ^ ((Nat.primeFactorsList n).length - 1) :=
          Finset.sum_le_sum (fun P hP => (ht P hP).2)
      _ = G.card * N ^ ((Nat.primeFactorsList n).length - 1) := by simp
      _ ≤ N * N ^ ((Nat.primeFactorsList n).length - 1) :=
          Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hPs)
      _ = N ^ (Nat.primeFactorsList n).length := by
          rw [← pow_succ']; congr 1; omega
end Formalism.HermitianLatticeCounting.P
