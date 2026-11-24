-- Prove2me | solution 1 for Formalism.GM.M.SSD.kap_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:09.861826+00:00
-- url     : https://prove2.me/submissions/75621fef-1934-4e47-8a01-274750a3dc86

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_coeff_kap
import Theorems.Thm_Formalism_GM_M_SSD_coeff_rename_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ τ K : Type} [Field K] [DecidableEq σ]
variable (e : τ → σ)
namespace Formalism.GM.M.SSD
theorem _root_.solution (he : Function.Injective e) (zm μ : σ →₀ ℕ) (hμ : ∀ x, μ (e x) = 0) (y : MvPolynomial τ K)
    (g : MvPolynomial σ K) (hg : ∀ w ∈ g.support, ∀ x, w (e x) = 0) :
    kap _ (F_inj e he zm μ) (monomial zm 1 * rename e y * g) = coeff μ g • y := by
  ext n
  rw [coeff_kap, coeff_smul, smul_eq_mul, mul_assoc, add_assoc, coeff_monomial_mul, one_mul,
    coeff_rename_mul e he n μ hμ y g hg, mul_comm]
end Formalism.GM.M.SSD
