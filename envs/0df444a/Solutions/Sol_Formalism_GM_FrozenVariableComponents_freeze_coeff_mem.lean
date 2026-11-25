-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.freeze_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:02:54.948013+00:00
-- url     : https://prove2.me/submissions/1f0a1d62-3e7e-4a8a-81f2-eeed45a93a3a

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__shift_360bf627fe39
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__pderiv_last_343f0ca2bb3b
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_full
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_hc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_diff_id
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__base_510735d22679
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
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (j : ℕ) (M : WithTop ℤ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ YCond p LL j M) (b : Fin r →₀ ℕ) :
    coeffη b (aeval (freezeSub p LL ρ) f) ∈ YCond p LL j M := by
  classical
  suffices H : ∀ n : ℕ, ∀ g ∈ Formalism.GM.M.YCond p LL j M, ∀ b' : Fin r →₀ ℕ,
      (∑ c ∈ Finset.univ.erase ρ, b' c) = n →
      coeffη b' (aeval (Formalism.GM.M.freezeSub p LL ρ) g) ∈ Formalism.GM.M.YCond p LL j M by
    exact H _ f hf b rfl
  intro n
  induction n with
  | zero =>
    intro g hg b' hb
    have hb' : b' = Finsupp.single ρ (b' ρ) := by
      ext c
      by_cases hc : c = ρ
      · subst hc
        simp
      · rw [Finsupp.single_apply, if_neg (Ne.symm hc)]
        exact (Finset.sum_eq_zero_iff.1 hb) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩)
    rw [hb', coeffη_base]
    exact ycond_hc p LL j M _ g hg
  | succ n ih =>
    intro g hg b' hb
    obtain ⟨c, hc, hbc⟩ : ∃ c ∈ Finset.univ.erase ρ, b' c ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [Finset.sum_eq_zero hcon] at hb
      exact Nat.succ_ne_zero n hb.symm
    have hcρ : c ≠ ρ := (Finset.mem_erase.1 hc).1
    obtain ⟨b0, rfl⟩ : ∃ b0, b' = b0 + Finsupp.single c 1 :=
      ⟨b' - Finsupp.single c 1,
        (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hbc))).symm⟩
    have e1 : ∑ c' ∈ Finset.univ.erase ρ, (b0 + Finsupp.single ρ 1 : Fin r →₀ ℕ) c' = ∑ c' ∈ Finset.univ.erase ρ, b0 c' :=
      Finset.sum_congr rfl (fun c' hc' => by
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.mem_erase.1 hc').1), add_zero])
    have e3 : ∑ c' ∈ Finset.univ.erase ρ, (Finsupp.single c 1 : Fin r →₀ ℕ) c' = 1 := by
      rw [Finset.sum_eq_single c (fun c' _ hc' => by rw [Finsupp.single_apply, if_neg (Ne.symm hc')])
          (fun h => absurd hc h), Finsupp.single_eq_same]
    have e2 : ∑ c' ∈ Finset.univ.erase ρ, (b0 + Finsupp.single c 1 : Fin r →₀ ℕ) c' =
        ∑ c' ∈ Finset.univ.erase ρ, b0 c' + 1 := by
      rw [Finset.sum_congr rfl (fun c' _ => Finsupp.add_apply b0 (Finsupp.single c 1) c'), Finset.sum_add_distrib, e3]
    have hs : ∑ c' ∈ Finset.univ.erase ρ, (b0 + Finsupp.single ρ 1 : Fin r →₀ ℕ) c' = n := by
      rw [e1]
      omega
    have key := ih _ (ycond_full p LL j M c ρ g hg) (b0 + Finsupp.single ρ 1) hs
    rw [← diff_id p LL ρ c hcρ g, ← pow_one (X (Fin.last N, ρ) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]),
      coeffη_shift, coeffη_pderiv_last] at key
    have hne : ((b0 c + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    have h2 := Submodule.smul_mem _ ((b0 c + 1 : ℕ) : ℚ_[p])⁻¹ key
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
end Formalism.GM.FrozenVariableComponents
