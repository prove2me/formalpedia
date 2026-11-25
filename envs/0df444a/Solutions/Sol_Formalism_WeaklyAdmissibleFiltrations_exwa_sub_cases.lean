-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwa_sub_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:25.426801+00:00
-- url     : https://prove2.me/submissions/70af8018-27ac-4001-be97-a65bdebfe361

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_Dl
import Theorems.Thm_P2M_Formalism_WeaklyAdmissibleFiltrations_exwaF___70203564a2ca

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (c : LL) (hc : c ≠ 0) (D' : Submodule LL (ZMod n → LL))
    (hD : (exwaF c hc).IsSub D') : D' = ⊥ ∨ D' = ⊤ := by
  by_cases h : ∃ i, (Pi.single i (1 : LL) : ZMod n → LL) ∈ D'
  · right
    obtain ⟨i, hi⟩ := h
    have step : ∀ j, (Pi.single j (1 : LL) : ZMod n → LL) ∈ D' →
        (Pi.single (j + 1) (1 : LL) : ZMod n → LL) ∈ D' := by
      intro j hj
      have h1 := hD.1 _ hj
      rw [exwaF_φ, exwaPhi_single] at h1
      have h2 := D'.smul_mem c⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    have all : ∀ k : ℕ, (Pi.single (i + k) (1 : LL) : ZMod n → LL) ∈ D' := by
      intro k
      induction k with
      | zero => simpa using hi
      | succ k ih => simpa [Nat.cast_succ, add_assoc] using step _ ih
    have allj : ∀ j, (Pi.single j (1 : LL) : ZMod n → LL) ∈ D' := by
      intro j
      have h1 := all (j - i).val
      have h2 : i + (((j - i).val : ℕ) : ZMod n) = j := by
        rw [ZMod.natCast_zmod_val]; ring
      rwa [h2] at h1
    rw [eq_top_iff, ← (Pi.basisFun LL (ZMod n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simpa using allj j
  · left
    simp only [not_exists] at h
    rw [hD.2]
    refine iSup_eq_bot.mpr fun i => ?_
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    rw [exwaF_Dl] at hx2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx2
    by_cases ha : a = 0
    · simp [ha]
    · exfalso
      apply h i
      have h3 := D'.smul_mem a⁻¹ hx1
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3
end Formalism.WeaklyAdmissibleFiltrations
