-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.FG_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:43.344911+00:00
-- url     : https://prove2.me/submissions/091257c6-0ab0-4ed1-a129-47d3ff927124

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_Bd_sub
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_mem_FG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (k : ℕ) (g a : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ∈ FG n K 0)
    (ha : a ∈ FG n K k) : g * a * g⁻¹ * a⁻¹ ∈ FG n K (k + 1) := by
  rw [mem_FG] at hg ha ⊢
  have hgi := inv_sub_one_bd g 0 hg
  have hai := inv_sub_one_bd a k ha
  have h1 : Bd 0 ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := (hgi.mono (Nat.zero_le _)).add Bd_one
    rwa [sub_add_cancel] at this
  have h2 : Bd 0 ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := (hai.mono (Nat.zero_le _)).add Bd_one
    rwa [sub_add_cancel] at this
  have hC : Bd (k + 1 + 1) (((g : Matrix (Fin n) (Fin n) K) - 1) * ((a : Matrix (Fin n) (Fin n) K) - 1) -
      ((a : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1)) :=
    (Bd.mul hg ha (by omega)).sub (Bd.mul ha hg (by omega))
  have hg1 : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha1 : (a : Matrix (Fin n) (Fin n) K) *
      ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : ((g * a * g⁻¹ * a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      (((g : Matrix (Fin n) (Fin n) K) - 1) * ((a : Matrix (Fin n) (Fin n) K) - 1) -
        ((a : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1)) *
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    calc _ = (g : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) -
          (a : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hg1, mul_one, ha1]
      _ = _ := by noncomm_ring
  rw [e]
  exact hC.mul (h1.mul h2 le_rfl) (by omega)
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
