-- Prove2me | solution 1 for Formalism.GM.euler_w_of_biHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:02.175821+00:00
-- url     : https://prove2.me/submissions/48dc7468-e18f-4589-8945-db9eb83268e0

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
namespace Formalism.GM
theorem _root_.solution {a b : ℕ} {g : MvPolynomial σ k} (h : BiHom w e a b g) :
    (∑ c, X (w c) * pderiv (w c) g) = (a : k) • g := by
  ext m
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  simp_rw [coeff_X_mul_pderiv']
  rw [← Finset.mul_sum]
  by_cases hm : coeff m g = 0
  · rw [hm]; simp
  · obtain ⟨h1, -⟩ := h m (MvPolynomial.mem_support_iff.mpr hm)
    rw [← h1, Nat.cast_sum]
    ring
end Formalism.GM
