-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.F_E_k
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:49.357802+00:00
-- url     : https://prove2.me/submissions/a0f5d46b-c062-4957-a1c6-650334616d0f

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


section
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {r : ℕ} (w e : Fin r → σ)
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
private theorem tieF_apply_lemma (g : MvPolynomial σ k) :
    tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by
  simp [tieF, LinearMap.sum_apply]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Polynomial Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
end
section
variable (p : ℕ) [Fact p.Prime]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM
open MvPolynomial Finset
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (α β : k) (Y : MvPolynomial σ k) (hW : EW w Y = α • Y) (hE : EW e Y = β • Y) :
    tieF w e (tieE w e Y) = tieE w e (tieF w e Y) + (α + β + r) • Y := by
  classical
  have hdE : ∀ c, pderiv (e c) (∑ c', X (w c') * X (e c') : MvPolynomial σ k) = X (w c) := by
    intro c
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, he.eq_iff, hwe]
  have hdW : ∀ c, pderiv (w c) (∑ c', X (w c') * X (e c') : MvPolynomial σ k) = X (e c) := by
    intro c
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, hw.eq_iff, fun a b => (hwe a b).symm]
  have key : ∀ c, pderiv (w c) (pderiv (e c) ((∑ c', X (w c') * X (e c')) * Y)) =
      (∑ c', X (w c') * X (e c')) * pderiv (w c) (pderiv (e c) Y) + X (e c) * pderiv (e c) Y + Y +
        X (w c) * pderiv (w c) Y := by
    intro c
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hdE, hdW, pderiv_X, Pi.single_eq_same]
    ring
  rw [tieF_apply_lemma, tieF_apply_lemma]
  simp only [tieE, LinearMap.mulLeft_apply]
  simp only [key]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ c, X (e c) * pderiv (e c) Y = β • Y := hE
  have h2 : ∑ c, X (w c) * pderiv (w c) Y = α • Y := hW
  rw [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_smul, add_smul,
    ← Nat.cast_smul_eq_nsmul k]
  abel
end Formalism.GM.GammaExpansion
