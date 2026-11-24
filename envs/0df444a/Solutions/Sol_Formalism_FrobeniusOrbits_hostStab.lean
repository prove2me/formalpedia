-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostStab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:26.028412+00:00
-- url     : https://prove2.me/submissions/75f7e6e6-31ea-4037-9784-6f53a350ae18

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_finrank_cmField
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostStab := by
  classical
  intro e q d hqd L _ _ ζ a b hL k g hg hlt Γ hΓ
  haveI := Fact.mk hg
  have hn := Galois.finrank_cmField hqd hL
  have key : ∀ δ : Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b), δ ^ g = 1 → δ = 1 := by
    intro δ hδ
    by_contra hne
    let M : Matrix (Fin k) (Fin k) (hostE ζ a b) := δ
    let f : Module.End ℚ (Fin k → hostE ζ a b) := (Matrix.mulVecLin M).restrictScalars ℚ
    have hfpow : ∀ n : ℕ, ∀ v, (f ^ n) v = (M ^ n).mulVec v := by
      intro n
      induction n with
      | zero => intro v; simp
      | succ n ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ]
        simp [f, Matrix.mulVec_mulVec]
    have hMg : M ^ g = 1 := by
      have h := congrArg (fun u : Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b) =>
        (u : Matrix (Fin k) (Fin k) (hostE ζ a b))) hδ
      simpa [M] using h
    have hf1 : f ^ g = 1 := by
      apply LinearMap.ext
      intro v
      rw [hfpow, hMg]
      simp
    have hfne : f ≠ 1 := by
      intro h
      apply hne
      apply Units.ext
      show M = 1
      ext i j
      have h2 := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
      simpa [f, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using h2
    have hQne : (Polynomial.X - 1 : Polynomial ℚ) * Polynomial.cyclotomic g ℚ ≠ 0 := by
      rw [mul_comm, Polynomial.cyclotomic_prime_mul_X_sub_one ℚ g]
      exact Polynomial.X_pow_sub_C_ne_zero hg.pos 1
    have hdvd : minpoly ℚ f ∣ (Polynomial.X - 1) * Polynomial.cyclotomic g ℚ := by
      apply minpoly.dvd
      rw [mul_comm, Polynomial.cyclotomic_prime_mul_X_sub_one ℚ g]
      simp [hf1]
    have hP0 : minpoly ℚ f ≠ 0 := fun h0 => hQne (zero_dvd_iff.1 (h0 ▸ hdvd))
    have hirr : Irreducible (Polynomial.cyclotomic g ℚ) := Polynomial.cyclotomic.irreducible_rat hg.pos
    by_cases hc : Polynomial.cyclotomic g ℚ ∣ minpoly ℚ f
    · have h1 := Polynomial.natDegree_le_of_dvd hc hP0
      have h2 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f)
        (LinearMap.charpoly_monic f).ne_zero
      rw [LinearMap.charpoly_natDegree] at h2
      rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hg] at h1
      have hdim : Module.finrank ℚ (Fin k → hostE ζ a b) = 2 ^ (e + 2) * k := by
        rw [Module.finrank_pi_fintype]
        simp [hn, mul_comm]
      have h3 := h1.trans h2
      rw [hdim] at h3
      exact absurd hlt (not_lt.2 h3)
    · have hcop : IsCoprime (Polynomial.cyclotomic g ℚ) (minpoly ℚ f) :=
        (Irreducible.coprime_iff_not_dvd hirr).2 hc
      have h1 : minpoly ℚ f ∣ Polynomial.X - 1 := hcop.symm.dvd_of_dvd_mul_right hdvd
      have h0 : Polynomial.aeval f (Polynomial.X - 1 : Polynomial ℚ) = 0 := by
        obtain ⟨r, hr⟩ := h1
        rw [hr, map_mul, minpoly.aeval, zero_mul]
      apply hfne
      simpa [sub_eq_zero] using h0
  rw [eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  obtain ⟨m, hm⟩ := hΓ γ hγ
  cases m with
  | zero => simpa using hm
  | succ m =>
    exfalso
    apply pow_ne_one_of_lt_orderOf (n := g ^ m) (x := γ) (pow_ne_zero _ hg.ne_zero)
      (by rw [hm, pow_succ]; exact lt_mul_of_one_lt_right (pow_pos hg.pos _) hg.one_lt)
    apply key
    rw [← pow_mul, ← pow_succ, ← hm, pow_orderOf_eq_one]
end Formalism.FrobeniusOrbits
