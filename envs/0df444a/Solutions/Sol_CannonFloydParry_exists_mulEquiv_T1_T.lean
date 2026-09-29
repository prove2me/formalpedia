-- Prove2me | solution 1 for CannonFloydParry.exists_mulEquiv_T1_T
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T20:18:57.316256+00:00
-- url     : https://prove2.me/submissions/52ae9fff-a4df-4c99-aa0d-e14883a6cb5a

import Theorems.Thm_CannonFloydParry_toCircle_mem_T_and_mapC_mem_T
import Theorems.Thm_CannonFloydParry_exists_surjective_T1_T
import Theorems.Thm_CannonFloydParry_isSimpleGroup_T1
import Mathlib

/-! Lemma 5.3 from Lemma 5.2; Corollary 5.9 from Lemma 5.3 and Theorem 5.8; the goal. -/

namespace CannonFloydParry.S5

/-- `C` moves `[0]`, so `C ≠ 1`. -/
lemma mapC_ne_one : mapC ≠ 1 := by
  intro h
  have h0 := congrArg (fun g : Equiv.Perm UnitAddCircle => AddCircle.equivIco (1 : ℝ) 0 (g 0)) h
  have hz : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by constructor <;> norm_num
  simp only [mapC, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.Perm.coe_one, id] at h0
  rw [show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) from rfl,
    AddCircle.equivIco_coe_eq hz] at h0
  have := congrArg Subtype.val h0
  simp [cIco, cFun] at this

/-- Corollary 5.9. -/
theorem exists_mulEquiv_T1_T' :
    ∃ e : T1 ≃* T, ∀ s, (e (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symT s := by
  obtain ⟨φ, hsurj, hφ⟩ := exists_surjective_T1_T
  have := isSimpleGroup_T1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker φ.normal_ker with hk | hk
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hk
    exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun s => hφ s⟩
  · exfalso
    obtain ⟨x, hx⟩ := hsurj ⟨mapC, toCircle_mem_T_and_mapC_mem_T.2⟩
    have : φ x = 1 := (MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top x)
    rw [this] at hx
    exact mapC_ne_one (congrArg Subtype.val hx).symm

end CannonFloydParry.S5

open CannonFloydParry

theorem solution :
    ∃ e : T1 ≃* T, ∀ s, (e (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symT s :=
  CannonFloydParry.S5.exists_mulEquiv_T1_T'
