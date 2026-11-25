-- Prove2me | solution 1 for Formalism.GM.extendWeightBounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:40:01.975081+00:00
-- url     : https://prove2.me/submissions/9d7be901-5b45-4e81-97d3-5942fa70d9f4

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_360bf627fe39
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_zero_bf4af767eaba
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_snoc_fwd
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_snoc_bwd
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__base_510735d22679
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_freeze_coeff_mem
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_weight_one__32b8ae2c834a
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_freeze_pol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb

set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.FrozenVariableComponents
namespace Formalism.GM
theorem _root_.solution : M.FreezeY := by
  intro p _ N r _ LL ρ n q J Mt hn hJ f hf
  have hf' : ∀ m ∈ f.support, Formalism.GM.M.MultiDeg LL m := by
    intro m hm
    have h := hf
    unfold Formalism.GM.M.Pol at h
    rw [mem_restrictSupport_iff] at h
    exact h (Finset.mem_coe.2 hm)
  have hhom : f.IsHomogeneous LL.total := by
    intro m hm
    show Finsupp.weight (fun _ : Fin N × Fin r => 1) m = LL.total
    rw [Formalism.GM.FrozenVariableComponents.weight_one']
    unfold Formalism.GM.M.Letters.total
    exact Finset.sum_congr rfl (fun i _ => hf' m (mem_support_iff.2 hm) i)
  have hcomp : homogeneousComponent LL.total f = f := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hhom), if_pos rfl]
  have hext := Formalism.GM.FrozenVariableComponents.freeze_pol p LL ρ n hn f hf
  unfold Formalism.GM.M.Y
  simp only [Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨-, hk⟩
    refine ⟨hext, fun k => ?_⟩
    apply Formalism.GM.FrozenVariableComponents.ycond_snoc_bwd p LL n (J k) (hJ k)
    intro b
    by_cases hb : Finsupp.single ρ (n - LL.total) ≤ b
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + Finsupp.single ρ (n - LL.total) :=
        ⟨b - Finsupp.single ρ (n - LL.total), (tsub_add_cancel_of_le hb).symm⟩
      unfold Formalism.GM.M.freeze
      rw [Formalism.GM.FrozenVariableComponents.coeffη_shift]
      exact Formalism.GM.FrozenVariableComponents.freeze_coeff_mem p LL ρ (J k) (Mt k) f (hk k) b'
    · unfold Formalism.GM.M.freeze
      rw [Formalism.GM.FrozenVariableComponents.coeffη_shift_zero b ρ _ hb]
      exact Submodule.zero_mem _
  · rintro ⟨-, hk⟩
    refine ⟨hf, fun k => ?_⟩
    have h1 := Formalism.GM.FrozenVariableComponents.ycond_snoc_fwd p LL n (J k) (hJ k) (Mt k)
      (Finsupp.single ρ LL.total + Finsupp.single ρ (n - LL.total)) _ (hk k)
    unfold Formalism.GM.M.freeze at h1
    rw [Formalism.GM.FrozenVariableComponents.coeffη_shift, Formalism.GM.FrozenVariableComponents.coeffη_base, hcomp] at h1
    exact h1
end Formalism.GM
