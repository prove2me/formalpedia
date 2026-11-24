-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dil_bound1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:29.338367+00:00
-- url     : https://prove2.me/submissions/57bda43a-1e23-4d74-bbd0-665af29c6b56

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_lrt_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_le_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_dl
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_dl
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inv_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ne_zero_of_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cc_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_one_le_K
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dl_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_unit_lr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {F : Mat k r → E} {A c : ℝ} {m : ℕ} (hA : 0 ≤ A) (hF : CCle A m F c) :
    CCle A m (dl t F) (((4 : ℝ) ^ r) ^ A * ((4 ^ r) ^ m * c)) := by
  have ht1 := ne_zero_of_mem_I h1
  have ht2 := ne_zero_of_mem_I h2
  have hc0 : 0 ≤ c := cc_nonneg hF
  unfold CCle at *
  refine ⟨ckOn_dl t ht1 ht2 hF.1, ?_⟩
  intro u v hu hv hl g hg
  have hunit := unit_lr h1 h2 hu hv
  set w' := (lr u v).map (adj t) with hw'
  set g' := (aDil k r t.1)⁻¹ * g * aDil k r t.2 with hg'
  have hgd : g' ∈ GV k r := dl_mem h1 h2 hg
  have hlen : w'.length ≤ m := by
    rw [hw', List.length_map, length_lr]
    exact hl
  have hb := bound_scaled (A := A) hF w' (by rw [hw', List.map_map]; exact lrt_lr u v)
    (fun x hx => by
      rw [hw', List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact adj_lie h1 h2 y (hunit y hy))
    hlen g' hgd
  have hpn : pn w' ≤ (4 ^ r) ^ m := by
    calc pn w' ≤ (4 ^ r) ^ w'.length := pn_le_pow w' (4 ^ r) (fun x hx => by
          rw [hw', List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact adj_le h1 h2 y (hunit y hy))
      _ ≤ (4 ^ r) ^ m := pow_le_pow_right₀ (one_le_K r) hlen
  have hW : dLR u v (dl t F) g = W w' F g' := by
    rw [dLR_eq, W_dl t ht1 ht2]
    rfl
  have hgn : gN g ^ A ≤ ((4 : ℝ) ^ r) ^ A * gN g' ^ A := by
    have := gN_dil (k := k) (inv_mem_I h1) h2 hA g
    rw [← aDil_inv k r t.1 ht1] at this
    exact this
  rw [hW]
  have hWn := norm_nonneg (W w' F g')
  calc gN g ^ A * ‖W w' F g'‖ ≤ ((4 : ℝ) ^ r) ^ A * gN g' ^ A * ‖W w' F g'‖ :=
      mul_le_mul_of_nonneg_right hgn hWn
    _ = ((4 : ℝ) ^ r) ^ A * (gN g' ^ A * ‖W w' F g'‖) := by ring
    _ ≤ ((4 : ℝ) ^ r) ^ A * (pn w' * c) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ((4 : ℝ) ^ r) ^ A * ((4 ^ r) ^ m * c) := by gcongr
end Formalism.FourierDecayAlt.P.B4
