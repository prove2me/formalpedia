-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.projAtOf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:01.056229+00:00
-- url     : https://prove2.me/submissions/59578b46-f12e-4097-abf8-f94512cf196c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_monomial_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_strip_monomial_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_monomial_single_add
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_fock_eq_zero_of
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_pow_mul_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_fock_pow_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_xH_le_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_grSpan_eq
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hX : ProjX) : ProjAtOf := by
  intro p _ K r _ LLw q J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 h1 h2 h3 h5 h6
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  have hgr := grSpan_eq LLw J M ρ w e e1 h1 h2 h3 h4 h5 h6 h7
  have hfree : ∀ g ∈ grSpan p LLw J M ρ w e,
      ∃ y ∈ XH p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        y ∈ FreeOf p (Fin.last K, ρ) ∧ g = X (Fin.last K, ρ) ^ e * y := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hgr g).mp hg
    exact ⟨y, hy, xH_le_free _ J _ ρ _ y hy, rfl⟩
  by_cases hme : m (Fin.last K, ρ) = e
  · have hle : Finsupp.single (Fin.last K, ρ) e ≤ m := by
      rw [Finsupp.single_le_iff]
      exact hme.ge
    obtain ⟨m', hm'v, hmm⟩ : ∃ m' : Fin (K + 1) × Fin r →₀ ℕ, m' (Fin.last K, ρ) = 0 ∧
        m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, by simp [hme], (add_tsub_cancel_of_le hle).symm⟩
    subst hmm
    have hMD : MultiDeg (setLast LLw (LLw.deg (Fin.last K) - e)) m' := by
      unfold MultiDeg at hm ⊢
      intro i
      have hi := hm i
      change _ = Function.update LLw.deg (Fin.last K) (LLw.deg (Fin.last K) - e) i
      rw [Function.update_apply]
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply,
        Prod.mk.injEq] at hi
      by_cases hik : i = Fin.last K
      · subst hik
        simp at hi
        rw [if_pos rfl]
        omega
      · have hik' : ¬ Fin.last K = i := fun h => hik h.symm
        simp [hik'] at hi
        rw [if_neg hik]
        exact hi
    obtain ⟨hP1, hP2, hP3⟩ := hPr' m' hMD hm'v
    have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial (Finsupp.single (Fin.last K, ρ) e + m') 1) = X (Fin.last K, ρ) ^ e * Pr' (monomial m' 1) := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, strip_monomial_eq _ _ _ hm'v]
    rw [hPr]
    refine ⟨(hgr _).mpr ⟨_, hP1, rfl⟩, ?_, ?_⟩
    · unfold IntPol at hP2 ⊢
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hP2
      refine LinearMap.mem_range.mpr ⟨X (Fin.last K, ρ) ^ e * z, ?_⟩
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) z = _ at hz
      change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (X (Fin.last K, ρ) ^ e * z) = _
      rw [map_mul, map_pow, map_X, hz, mul_smul_comm]
    · intro g hg
      obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
      rw [fock_pow_mul _ _ _ _ hyf, hP3 y hy, monomial_single_add, fock_pow_mul _ _ _ _ hyf]
  · have hPr : ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e)) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e)
        (monomial m 1) = 0 := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, strip_monomial_ne _ _ _ hme, map_zero, map_zero]
    rw [hPr]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, hyf, rfl⟩ := hfree g hg
    rw [fock_eq_zero_of _ _ (fun n => Or.inr (coeff_zero n)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · subst hn
      exact Or.inl (coeff_pow_mul_ne _ _ _ hyf _ hme)
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]
end Formalism.InvariantFactorPaths.L4
