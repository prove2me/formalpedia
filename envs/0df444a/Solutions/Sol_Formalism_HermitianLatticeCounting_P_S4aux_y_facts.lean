-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.y_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:38.607594+00:00
-- url     : https://prove2.me/submissions/edd0e8e5-ea29-4377-95c7-a9193e237715

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (q ρ : ℕ) (hq : 2 ≤ q) (hρ : 4 ≤ ρ) :
    (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹ ∧ 0 ≤ (q : ℝ) ^ (1 - (ρ : ℤ)) ∧
      (q : ℝ) ^ (1 - (ρ : ℤ)) ≤ 1 / 8 := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (1 - (ρ : ℤ)) = q * ((q : ℝ) ^ ρ)⁻¹ := by
    rw [zpow_sub₀ hq0.ne', zpow_one, zpow_natCast, div_eq_mul_inv]
  refine ⟨h1, by positivity, ?_⟩
  obtain ⟨ρ', rfl⟩ : ∃ ρ', ρ = ρ' + 4 := ⟨ρ - 4, by omega⟩
  have h2 : (q : ℝ) * ((q : ℝ) ^ (ρ' + 4))⁻¹ = ((q : ℝ) ^ (ρ' + 3))⁻¹ := by
    rw [pow_succ (q : ℝ) (ρ' + 3)]; field_simp
  rw [h1, h2, one_div]
  apply inv_anti₀ (by norm_num)
  calc (8 : ℝ) = 2 ^ 3 := by norm_num
    _ ≤ (q : ℝ) ^ 3 := by gcongr
    _ ≤ (q : ℝ) ^ (ρ' + 3) := pow_le_pow_right₀ (by linarith) (by omega)
end Formalism.HermitianLatticeCounting.P.S4aux
