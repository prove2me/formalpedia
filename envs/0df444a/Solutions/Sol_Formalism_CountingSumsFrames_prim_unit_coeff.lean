-- Prove2me | solution 1 for Formalism.CountingSumsFrames.prim_unit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:28.921736+00:00
-- url     : https://prove2.me/submissions/ceaa554e-bf23-47c5-9ff2-63563c5a65c3

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_intPol_norm
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hz : z ∈ YZ p (r := r) LL J M)
    (hprim : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) :
    ∃ m, ‖coeff m z‖ = 1 := by
  have hzI : z ∈ IntPol p (Fin N × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).2
  by_contra hc
  push Not at hc
  have hlt : ∀ m, ‖coeff m z‖ < 1 := fun m => lt_of_le_of_ne (intPol_norm z hzI m) (hc m)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set x := (p : ℚ_[p])⁻¹ • z with hx
  have hxI : x ∈ IntPol p (Fin N × Fin r) := by
    refine mem_intPol_of_norm _ fun m => ?_
    rw [hx, coeff_smul, smul_eq_mul, norm_mul, norm_inv, Padic.norm_p, inv_inv]
    have h1 := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (coeff m z) (-1)).mpr (by simpa using hlt m)
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    rw [zpow_neg_one] at h1
    calc (p : ℝ) * ‖coeff m z‖ ≤ p * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h1 hp.le
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hxY : x ∈ YZ p (r := r) LL J M := by
    have hzY := (Submodule.mem_inf.mp hz).1
    have hzP := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1
    refine Submodule.mem_inf.mpr ⟨?_, Submodule.mem_inf.mpr ⟨?_, hxI⟩⟩
    · exact (Y p LL J M).smul_mem _ hzY
    · exact (Pol p r LL).smul_mem _ hzP
  have hzx : z = (p : ℤ_[p]) • x := by
    rw [hx, ← algebraMap_smul ℚ_[p] (p : ℤ_[p]), smul_smul]
    simp [hp0]
  have hu := hprim _ x hxY hzx
  rw [PadicInt.isUnit_iff, PadicInt.norm_p] at hu
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have := inv_lt_one_of_one_lt₀ this
  linarith
end Formalism.CountingSumsFrames
