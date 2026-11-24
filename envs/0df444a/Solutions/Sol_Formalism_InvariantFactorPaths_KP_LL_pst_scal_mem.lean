-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.pst_scal_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:04.815924+00:00
-- url     : https://prove2.me/submissions/50d756d2-8c64-4382-ad98-5dafe6255cb5

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
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
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {p : ℕ} [Fact p.Prime] {σ : Type} (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (a u m j k : ℕ) (hk : k ≤ j) (hu : a + Nat.log p j ≤ u) (s : ℚ_[p]) (hs : ‖s‖ ≤ 1)
    (y : MvPolynomial σ ℚ_[p])
    (hy : (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) ∈ Λ) :
    ((s * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y) ∈ Λ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp1
  have e1 : (s * (p : ℚ_[p]) ^ (a + Nat.log p j + d) *
      (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y =
      (s * (p : ℚ_[p]) ^ d * ((p : ℚ_[p]) ^ (Nat.log p j) * (((j.choose k : ℕ) : ℚ_[p]))⁻¹)) •
        (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) := by
    rw [smul_smul, mul_inv, pow_add, pow_add]
    congr 1
    ring
  rw [e1]
  refine smul_mem_of_norm Λ ?_ hy
  have hpn : ∀ t : ℕ, ‖(p : ℚ_[p]) ^ t‖ = ((p : ℝ) ^ t)⁻¹ := by
    intro t
    rw [norm_pow, Padic.norm_p, inv_pow]
  rw [norm_mul, norm_mul, norm_mul, hpn, hpn]
  have h1 : ((p : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
  have h2 : ((p : ℝ) ^ (Nat.log p j))⁻¹ * ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ 1 := by
    have := PhiIntegrality.norm_choose_inv_le (p := p) j k hk
    rw [inv_mul_le_iff₀ (pow_pos hp0 _), mul_one]
    exact this
  have h3 : ‖s‖ * ((p : ℝ) ^ d)⁻¹ ≤ 1 :=
    mul_le_one₀ hs (inv_nonneg.mpr (pow_pos hp0 _).le) h1
  exact mul_le_one₀ h3 (mul_nonneg (inv_nonneg.mpr (pow_pos hp0 _).le) (norm_nonneg _)) h2
end Formalism.InvariantFactorPaths.KP.LL
