-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.gauss_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:38.395842+00:00
-- url     : https://prove2.me/submissions/cb7cc054-1b96-48d7-9ca0-6204524fc3e6

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_gauss_sum_ring
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_trace_surj

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (h2 : Module.finrank K L = 2) (n : ℕ) (Ph : Matrix (Fin n) (Fin n) L)
    (hPh : IsUnit Ph.det) (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (φ : (Fin n → L) → ℂ)
    (hφ : ∀ u, ‖φ u‖ = 1)
    (hadd : ∀ u d, φ (u + d) = φ u * φ d *
      ψ (Algebra.trace K L (∑ i, ∑ j, u i * Ph i j * d j ^ Fintype.card K))) :
    ‖∑ u, φ u‖ ≤ (Fintype.card K : ℝ) ^ n := by
  let ψ' : AddChar L ℂ := ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom
  have h := @hermitian_gauss_sum_ring L _ _ (frobStar h2) n Ph ψ' φ hPh hφ hadd
  have hY : Nat.card {y : L // ∀ c, ψ' (c * y) = 1} ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    have h0 : ∀ y : {y : L // ∀ c, ψ' (c * y) = 1}, y.1 = 0 := by
      intro y
      by_contra hy
      apply hψ
      ext k
      obtain ⟨z, rfl⟩ := trace_surj (K := K) (L := L) k
      have := y.2 (z / y.1)
      rw [div_mul_cancel₀ _ hy] at this
      rw [AddChar.zero_apply]
      exact this
    exact ⟨fun y y' => Subtype.ext (by rw [h0 y, h0 y'])⟩
  have hY' : (Nat.card {y : L // ∀ c, ψ' (c * y) = 1} : ℝ) ^ n ≤ 1 := by
    apply pow_le_one₀ (Nat.cast_nonneg _)
    exact_mod_cast hY
  have h3 : ‖∑ u, φ u‖ ^ 2 ≤ ((Fintype.card K : ℝ) ^ n) ^ 2 := by
    calc _ ≤ _ := h
      _ ≤ (Fintype.card L : ℝ) ^ n * 1 := by gcongr
      _ = _ := by rw [card_L h2]; push_cast; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
end Formalism.HermitianLatticeCounting.P.S4aux
