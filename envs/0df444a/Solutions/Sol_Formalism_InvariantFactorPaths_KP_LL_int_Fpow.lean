-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.int_Fpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:04.882265+00:00
-- url     : https://prove2.me/submissions/21674659-fa8f-459c-90dc-686731402f86

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_smul
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_commute_pderiv
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_D
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_Fsum
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_norm_choose_inv_le
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_intPol_iff_bnd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {τ : Type} {r : ℕ} (L m : ℕ) (hmL : Nat.log p m ≤ L) (w e : Fin r → τ)
    {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) y) ∈ IntPol p τ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  set Mc : ℝ := (p : ℝ) ^ L with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ m, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hmL))
  let Dc : Fin r → (MvPolynomial τ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial τ ℚ_[p]) (MvPolynomial τ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (Dc a) (Dc b) := by
    intro a b
    simp only [Dc, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum Dc hcomm (fun a k => contr_D _ _ k) hM1 m hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, Dc c := rfl
  have hb : Bnd (p := p) 1 y := (intPol_iff_bnd y).mp hy
  have h1 := hF m le_rfl 1 zero_le_one y hb
  rw [← hFeq] at h1
  rw [intPol_iff_bnd, ← smul_smul]
  have h2 := bnd_smul ((p : ℚ_[p]) ^ (r * L)) h1
  intro μ
  refine (h2 μ).trans (le_of_eq ?_)
  rw [Padic.norm_p_pow, hMc, one_mul, ← pow_mul, zpow_neg, zpow_natCast, mul_comm L r]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by positivity))
end Formalism.InvariantFactorPaths.KP.LL
