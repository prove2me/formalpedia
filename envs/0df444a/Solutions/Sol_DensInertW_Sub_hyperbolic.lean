-- Prove2me | solution 1 for DensInertW.Sub.hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:59.908712+00:00
-- url     : https://prove2.me/submissions/46cb7f73-07bc-4934-93fc-5a70b71e19ab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Theorems.Thm_DensInertW_Sub_q_ne_zero_of_inv
import Theorems.Thm_DensInertW_Sub_hf_sub_left
import Theorems.Thm_DensInertW_Sub_hfL_apply
import Theorems.Thm_DensInertW_Sub_hf_add_right
import Theorems.Thm_DensInertW_Sub_hf_smul_right
import Theorems.Thm_DensInertW_Sub_hf_symm
import Theorems.Thm_DensInertW_Sub_finrank_inf_ker_add_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW.Sub
theorem _root_.solution (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (hinv : ∀ a : L, (a ^ q) ^ q = a) (hM : ∀ k l, M l k = M k l ^ q)
    (htrs : ∀ s : L, s ^ q = s → ∃ t : L, t + t ^ q = s)
    (W : Submodule L (Fin n → L)) (hW : NonDeg q M W) (x : Fin n → L) (hx : x ∈ W)
    (hx0 : x ≠ 0) (hxx : hf q M x x = 0) :
    ∃ y ∈ W, hf q M x y = 1 ∧ hf q M y y = 0 ∧
      finrank L ↥(W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)) + 2 =
        finrank L ↥W ∧
      NonDeg q M (W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)) := by
  have hq := q_ne_zero_of_inv hinv
  obtain ⟨v, hv, hz⟩ : ∃ v ∈ W, hf q M x v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (hW x hx hc)
  set y1 := ((hf q M x v)⁻¹) ^ q • v with hy1
  have hy1W : y1 ∈ W := W.smul_mem _ hv
  have hxy1 : hf q M x y1 = 1 := by
    rw [hy1, hf_smul_right, hinv, inv_mul_cancel₀ hz]
  clear_value y1
  have hy1x : hf q M y1 x = 1 := by
    rw [hf_symm hadd hinv hM x y1, hxy1, one_pow]
  have hs : (hf q M y1 y1) ^ q = hf q M y1 y1 := (hf_symm hadd hinv hM y1 y1).symm
  have hneg : (-hf q M y1 y1) ^ q = -hf q M y1 y1 := by
    have h := hadd (hf q M y1 y1) (-hf q M y1 y1)
    rw [add_neg_cancel, zero_pow hq] at h
    linear_combination -h - hs
  obtain ⟨t, ht⟩ := htrs _ hneg
  set y := y1 + t • x with hy
  have hyW : y ∈ W := W.add_mem hy1W (W.smul_mem _ hx)
  clear_value y
  have hxy : hf q M x y = 1 := by
    rw [hy, hf_add_right hadd, hf_smul_right, hxx, mul_zero, add_zero, hxy1]
  have hyy : hf q M y y = 0 := by
    rw [hy, hf_add_left, hf_add_right hadd, hf_add_right hadd, hf_smul_left, hf_smul_left,
      hf_smul_right, hf_smul_right, hxx, hy1x, hxy1]
    linear_combination ht
  have hyx : hf q M y x = 1 := by
    rw [hf_symm hadd hinv hM x y, hxy, one_pow]
  refine ⟨y, hyW, hxy, hyy, ?_, ?_⟩
  · have h1 := finrank_inf_ker_add_one W (hfL q M y) x hx
      (by rw [hfL_apply, hxy]; exact one_ne_zero)
    have h2 := finrank_inf_ker_add_one (W ⊓ LinearMap.ker (hfL q M y)) (hfL q M x) y
      (Submodule.mem_inf.2 ⟨hyW, by rw [LinearMap.mem_ker, hfL_apply, hyy]⟩)
      (by rw [hfL_apply, hyx]; exact one_ne_zero)
    rw [inf_right_comm]
    omega
  · intro w hw hperp
    have hw' := Submodule.mem_inf.1 hw
    have hw'' := Submodule.mem_inf.1 hw'.1
    have hwx : hf q M w x = 0 := LinearMap.mem_ker.1 hw''.2
    have hwy : hf q M w y = 0 := LinearMap.mem_ker.1 hw'.2
    apply hW w hw''.1
    intro u hu
    have hu' : u - hf q M u y • x - hf q M u x • y ∈
        W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y) := by
      refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2
        ⟨W.sub_mem (W.sub_mem hu (W.smul_mem _ hx)) (W.smul_mem _ hyW), ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, hfL_apply, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left,
          hxx, hyx]
        ring
      · rw [LinearMap.mem_ker, hfL_apply, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left,
          hxy, hyy]
        ring
    have h0 := hperp _ hu'
    have hsplit : u = (u - hf q M u y • x - hf q M u x • y) + hf q M u y • x + hf q M u x • y := by
      abel
    rw [hsplit, hf_add_right hadd, hf_add_right hadd, h0, hf_smul_right, hf_smul_right, hwx, hwy]
    ring
end DensInertW.Sub
