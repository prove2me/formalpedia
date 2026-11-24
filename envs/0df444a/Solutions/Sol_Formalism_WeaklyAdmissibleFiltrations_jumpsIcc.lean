-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.jumpsIcc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:07.837369+00:00
-- url     : https://prove2.me/submissions/3223ec89-4659-4764-8789-774a3df7f9f9

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_FilPhi_fil_le_fil_of_le

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
open FilPhi
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : JumpsIcc := by
  intro LL _ D _ _ n Emb _ F τ l h
  constructor
  · intro hJ
    have hno : ∀ a, a ∉ Set.Icc l h → F.Fil τ (a + 1) = F.Fil τ a := by
      intro a ha
      by_contra hne
      exact ha (hJ a hne)
    constructor
    ·
      have key : ∀ k : ℕ, F.Fil τ (l - k) = F.Fil τ l := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hk : (l - ((k + 1 : ℕ) : ℤ)) ∉ Set.Icc l h := by
            intro hm; have := hm.1; push_cast at this; omega
          have e := hno _ hk
          have : l - ((k + 1 : ℕ) : ℤ) + 1 = l - (k : ℤ) := by push_cast; ring
          rw [this] at e
          rw [← e, ih]
      have hlo := F.Fil_lo τ (l - ((l - min F.lo l).toNat : ℕ)) (by omega)
      rw [key] at hlo
      exact hlo
    ·
      have key : ∀ k : ℕ, F.Fil τ (h + 1 + k) = F.Fil τ (h + 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hk : (h + 1 + (k : ℤ)) ∉ Set.Icc l h := by
            intro hm; have := hm.2; omega
          have e := hno _ hk
          have : h + 1 + ((k + 1 : ℕ) : ℤ) = h + 1 + (k : ℤ) + 1 := by push_cast; ring
          rw [this, e, ih]
      have hhi := F.Fil_hi τ (h + 1 + ((F.hi - (h + 1)).toNat : ℕ)) (by omega)
      rw [key] at hhi
      exact hhi
  · rintro ⟨hl, hh⟩ a ha
    by_contra hm
    apply ha
    rcases (not_and_or.mp hm) with hal | hah
    · have hal : a + 1 ≤ l := by omega
      apply le_antisymm (F.Fil_anti τ a)
      calc F.Fil τ a ≤ F.Dl (F.letter τ) := F.Fil_le τ a
        _ = F.Fil τ l := hl.symm
        _ ≤ F.Fil τ (a + 1) := F.fil_le_fil_of_le τ hal
    · have hah : h + 1 ≤ a := by omega
      have h1 : F.Fil τ a = ⊥ := le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ hah)
      have h2 : F.Fil τ (a + 1) = ⊥ :=
        le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ (by omega : h + 1 ≤ a + 1))
      rw [h1, h2]
end Formalism.WeaklyAdmissibleFiltrations
