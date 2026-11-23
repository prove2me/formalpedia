-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resOntoK_of_resSat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:52.634955+00:00
-- url     : https://prove2.me/submissions/e4d31961-475b-4cd4-b4e3-0553f7a69f8e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_p_pow_ne_zero
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Gen
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end Gen
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
private theorem exists_prime_pow_smul_mem_intPol {τ : Type} (x : MvPolynomial τ ℚ_[p]) :
    ∃ n : ℕ, ((p : ℚ_[p]) ^ n) • x ∈ IntPol p τ := by
  classical
  refine MvPolynomial.induction_on' x (fun u a => ?_) (fun f g hf hg => ?_)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖a‖
      (show (1 : ℝ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt)
    refine ⟨n, ?_⟩
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hpos : (0 : ℝ) < (p : ℝ) ^ n := pow_pos hp0 n
    have hle : ‖(p : ℚ_[p]) ^ n * a‖ ≤ 1 := by
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      calc ((p : ℝ) ^ n)⁻¹ * ‖a‖ ≤ ((p : ℝ) ^ n)⁻¹ * (p : ℝ) ^ n := by gcongr
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    unfold IntPol
    rw [LinearMap.mem_range]
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[p], (c : ℚ_[p]) = (p : ℚ_[p]) ^ n * a := ⟨⟨_, hle⟩, rfl⟩
    refine ⟨monomial u c, ?_⟩
    rw [smul_monomial, smul_eq_mul, ← hc]
    show MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) _ = _
    rw [map_monomial]
    rfl
  · obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    refine ⟨a + b, ?_⟩
    have key : ((p : ℚ_[p]) ^ (a + b)) • (f + g) =
        ((p : ℤ_[p]) ^ b) • (((p : ℚ_[p]) ^ a) • f) + ((p : ℤ_[p]) ^ a) • (((p : ℚ_[p]) ^ b) • g) := by
      rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ b) (((p : ℚ_[p]) ^ a) • f),
        ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ a) (((p : ℚ_[p]) ^ b) • g)]
      simp only [map_pow, map_natCast, smul_smul, smul_add, ← pow_add, add_comm b a]
    rw [key]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (h : ResSat p LL J M ρ) : ResOntoK p LL J M ρ := by
  intro x hx
  obtain ⟨n, hn⟩ := exists_prime_pow_smul_mem_intPol (p := p) x
  obtain ⟨h', hY, -, hinit⟩ := h _ (Submodule.smul_mem _ _ hx) hn
  refine ⟨((p : ℚ_[p]) ^ n)⁻¹ • h', Submodule.smul_mem _ _ hY, ?_⟩
  rw [initPart_smul, hinit, smul_smul, inv_mul_cancel₀ (p_pow_ne_zero n), one_smul]
end Formalism.InvariantFactorPaths.L4
