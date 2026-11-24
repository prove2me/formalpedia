-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_Fsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.603004+00:00
-- url     : https://prove2.me/submissions/e2d23779-04c0-4ec9-ac53-8c61745cb550

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_norm_choose_inv_le
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_smul_mem_of_norm


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
theorem _root_.solution {σ ι : Type} [DecidableEq ι]
    (Dc : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (hcomm : ∀ a b, Commute (Dc a) (Dc b))
    (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hdiv : ∀ a k l, ∀ x ∈ Λ l, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (Dc a ^ k) x) ∈ Λ (l + k))
    (L n : ℕ) (hn : Nat.log p n ≤ L) (S : Finset ι) :
    ∀ j ≤ n, ∀ l, ∀ x ∈ Λ l,
      (((p : ℚ_[p]) ^ (S.card * L) * ((j.factorial : ℚ_[p]) ^ 2)⁻¹) • ((∑ c ∈ S, Dc c) ^ j) x) ∈ Λ (l + j) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  induction S using Finset.induction_on with
  | empty =>
    intro j _ l x hx
    rcases j with _ | j
    · simpa using hx
    · simp
  | insert a S ha ih =>
    intro j hj l x hx
    have hc : Commute (Dc a) (∑ c ∈ S, Dc c) := Commute.sum_right _ _ _ (fun c _ => hcomm a c)
    rw [Finset.sum_insert ha, hc.add_pow j, Finset.card_insert_of_notMem ha,
      LinearMap.sum_apply, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hkj : k ≤ j := by rw [Finset.mem_range] at hk; omega
    have hfac := Nat.choose_mul_factorial_mul_factorial hkj
    have hne : ((j.choose k : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkj).ne'
    have hk0 : ((k.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    have hjk0 : (((j - k).factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have key : (((j.factorial : ℚ_[p]) ^ 2))⁻¹ * ((j.choose k : ℕ) : ℚ_[p]) =
        (((j.choose k : ℕ) : ℚ_[p]))⁻¹ * ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ *
          ((((j - k).factorial : ℚ_[p]) ^ 2))⁻¹) := by
      rw [← hfac]
      push_cast
      field_simp
    have eq : ((p : ℚ_[p]) ^ ((S.card + 1) * L) * ((j.factorial : ℚ_[p]) ^ 2)⁻¹) •
        (Dc a ^ k * (∑ c ∈ S, Dc c) ^ (j - k) *
          ((j.choose k : ℕ) : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])) x =
        ((p : ℚ_[p]) ^ L * (((j.choose k : ℕ) : ℚ_[p]))⁻¹) • ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (Dc a ^ k)
          (((p : ℚ_[p]) ^ (S.card * L) * (((j - k).factorial : ℚ_[p]) ^ 2)⁻¹) •
            ((∑ c ∈ S, Dc c) ^ (j - k)) x)) := by
      simp only [Module.End.mul_apply, Module.End.natCast_apply,
        map_smul, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul]
      congr 1
      rw [mul_assoc, key, add_mul, one_mul, pow_add]
      ring
    rw [eq]
    have h1 := ih (j - k) (by omega) l x hx
    have h2 := hdiv a k _ _ h1
    rw [show l + (j - k) + k = l + j by omega] at h2
    refine smul_mem_of_norm _ ?_ h2
    rw [norm_mul, norm_pow, Padic.norm_p]
    have h3 : ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ L :=
      (norm_choose_inv_le j k hkj).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hn))
    calc ((p : ℝ)⁻¹) ^ L * ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ ((p : ℝ)⁻¹) ^ L * (p : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
end Formalism.InvariantFactorPaths.KP.LL
