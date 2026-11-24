-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.fock_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:44:52.878707+00:00
-- url     : https://prove2.me/submissions/11a2952d-354a-4ddb-a49e-1acd4bab39a7

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_smul_right
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_sum_right
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_X_pow_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_tiePhi_eq
import Theorems.Thm_Formalism_GM_GammaExpansion_main_expand
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r)
    (q y : MvPolynomial σ ℚ_[p]) (K : ℕ) (hq : ∀ s ∈ q.support, s (e ρ) ≤ K) (o' n' z' s m : ℕ) :
    M.fock p (X (e ρ) ^ m * y) ((tieE w e ^ s) (tiePhi w e o' n' z' (X (e ρ) ^ m * q))) =
      ∑ j ∈ range (o' + 1), cph ℚ_[p] (o' + n' + r + z' - 1) j * ((m.factorial : ℚ_[p]) *
        ∑ i ∈ range (s + j + 1), ∑ t ∈ range (K + 1),
          (((m.choose i * (m - i).choose t : ℕ) : ℚ_[p]) * ((s + j).descFactorial i : ℚ_[p]) /
            ((i + t).factorial : ℚ_[p])) *
          M.fock p y (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s + j - i) *
            (tieF w e ^ j) (X (e ρ) ^ (i + t) * (Dp (e ρ) ^ t) q))) := by
  rw [fock_X_pow_mul, tiePhi_eq, map_sum, map_sum, fock_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hEE : (tieE w e ^ s) ((tieE w e ^ j) ((tieF w e ^ j) (X (e ρ) ^ m * q))) =
      (tieE w e ^ (s + j)) ((tieF w e ^ j) (X (e ρ) ^ m * q)) := by
    rw [pow_add] <;> rfl
  rw [map_smul, map_smul, hEE, main_expand he hwe ρ q K hq (s + j) j m, fock_smul_right, fock_smul_right,
    fock_sum_right]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fock_sum_right]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [fock_smul_right]
end Formalism.GM.GammaExpansion
