-- Prove2me | solution 1 for CannonFloydParry.closure_range_symT_eq_T_and_relations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T19:57:50.02628+00:00
-- url     : https://prove2.me/submissions/55575f47-1442-43f7-8d55-f9a7e38f4c1c

import Definitions.Def_CannonFloydParry_T
import Mathlib
import Theorems.Thm_CannonFloydParry_mem_T_iff_isThompsonCircle
import Theorems.Thm_CannonFloydParry_toCircle_mem_T_and_mapC_mem_T
import Theorems.Thm_CannonFloydParry_exists_toCircle_eq_of_mem_T_of_apply_zero
import Theorems.Thm_CannonFloydParry_exists_mem_F_map_partition
import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F

/-! `toCircle` is an injective group homomorphism from the order isomorphisms of `[0,1]`. -/

namespace CannonFloydParry.S5

lemma icoPerm_mul (f g : UI ≃o UI) : icoPerm (f * g) = icoPerm f * icoPerm g := by
  ext x; rfl

lemma toCircle_mul (f g : UI ≃o UI) : toCircle (f * g) = toCircle f * toCircle g := by
  ext x
  simp only [toCircle, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, icoPerm_mul]

lemma toCircle_one : toCircle 1 = 1 := by
  ext x
  simp only [toCircle, Equiv.trans_apply, Equiv.Perm.coe_one, id]
  have : icoPerm (1 : UI ≃o UI) = 1 := by ext y; rfl
  rw [this, Equiv.Perm.coe_one, id, Equiv.symm_apply_apply]

/-- `toCircle` as a group homomorphism. -/
noncomputable def toCircleHom : (UI ≃o UI) →* Equiv.Perm UnitAddCircle where
  toFun := toCircle
  map_one' := toCircle_one
  map_mul' := toCircle_mul

@[simp] lemma toCircleHom_apply (f : UI ≃o UI) : toCircleHom f = toCircle f := rfl

end CannonFloydParry.S5

/-! Evaluating `A`, `B`, `C` and their inverses on `[0,1)` representatives of the circle. -/

namespace CannonFloydParry.S5

/-- The representative in `[0,1)` of a point of the circle. -/
noncomputable def ico (x : UnitAddCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

lemma ico_nonneg (x : UnitAddCircle) : 0 ≤ ico x := (AddCircle.equivIco (1 : ℝ) 0 x).2.1
lemma ico_lt_one (x : UnitAddCircle) : ico x < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 x).2.2
  unfold ico
  linarith

lemma perm_ext {σ τ : Equiv.Perm UnitAddCircle} (h : ∀ x, ico (σ x) = ico (τ x)) : σ = τ := by
  ext x
  exact (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext (h x))

lemma ico_symm (y : Set.Ico (0 : ℝ) (0 + 1)) : ico ((AddCircle.equivIco (1 : ℝ) 0).symm y) = y := by
  simp [ico]

lemma ico_toCircle (f : UI ≃o UI) (x : UnitAddCircle) :
    ico (toCircle f x) = (f ⟨ico x, ico_nonneg x, (ico_lt_one x).le⟩ : ℝ) := by
  simp only [toCircle, Equiv.trans_apply, ico_symm]
  rfl

/-! Piecewise formulas. -/

lemma aInv_of_mem1 {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1/4) : aInv y = 2 * y := by
  unfold aInv; split_ifs <;> linarith
lemma aInv_of_mem2 {y : ℝ} (h0 : 1/4 ≤ y) (h1 : y ≤ 1/2) : aInv y = y + 1/4 := by
  unfold aInv; split_ifs <;> linarith
lemma aInv_of_mem3 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y ≤ 1) : aInv y = (y + 1) / 2 := by
  unfold aInv; split_ifs <;> linarith
lemma bInv_of_mem0 {y : ℝ} (h1 : y ≤ 1/2) : bInv y = y := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem1 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y ≤ 5/8) : bInv y = 2 * y - 1/2 := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem2 {y : ℝ} (h0 : 5/8 ≤ y) (h1 : y ≤ 3/4) : bInv y = y + 1/8 := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem3 {y : ℝ} (h0 : 3/4 ≤ y) (h1 : y ≤ 1) : bInv y = (y + 1) / 2 := by
  unfold bInv; split_ifs <;> linarith
lemma cFun_of_mem1 {x : ℝ} (h1 : x < 1/2) : cFun x = x / 2 + 3/4 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem2 {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x < 3/4) : cFun x = 2 * x - 1 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem3 {x : ℝ} (h0 : 3/4 ≤ x) : cFun x = x - 1/4 := by
  unfold cFun; split_ifs <;> linarith
lemma cInv_of_mem3 {y : ℝ} (h0 : 3/4 ≤ y) : cInv y = 2 * y - 3/2 := by
  unfold cInv; split_ifs <;> linarith

lemma aInv_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ aInv y ∧ aInv y ≤ 1 := by
  unfold aInv; split_ifs <;> constructor <;> linarith
lemma bInv_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ bInv y ∧ bInv y ≤ 1 := by
  unfold bInv; split_ifs <;> constructor <;> linarith

/-! The generators and their inverses on representatives. -/

lemma ico_A (x : UnitAddCircle) : ico (symT FormalABC.A x) = aFun (ico x) := by
  simp only [symT, ico_toCircle, mapA, restrict_coe, lineA_apply]

lemma ico_B (x : UnitAddCircle) : ico (symT FormalABC.B x) = bFun (ico x) := by
  simp only [symT, ico_toCircle, mapB, restrict_coe, lineB_apply]

lemma ico_C (x : UnitAddCircle) : ico (symT FormalABC.C x) = cFun (ico x) := by
  simp only [symT, mapC, Equiv.trans_apply, ico_symm]
  rfl

lemma inv_apply_eq_of {σ : Equiv.Perm UnitAddCircle} {x z : UnitAddCircle} (h : σ z = x) :
    σ⁻¹ x = z := by
  rw [Equiv.Perm.inv_eq_iff_eq]; exact h.symm

lemma ico_Ainv (x : UnitAddCircle) : ico ((symT FormalABC.A)⁻¹ x) = aInv (ico x) := by
  obtain ⟨h0, h1⟩ := aInv_mem (ico_nonneg x) (ico_lt_one x).le
  have hlt : aInv (ico x) < 0 + 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · simpa using h
    · exfalso
      have := aFun_aInv (ico x); rw [h] at this
      rw [aFun_of_mem3 (by norm_num) le_rfl] at this
      linarith [ico_lt_one x]
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨aInv (ico x), h0, hlt⟩
  have hz : symT FormalABC.A z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.A z) = ico x
    rw [ico_A, ico_symm]
    exact aFun_aInv (ico x)
  rw [inv_apply_eq_of hz, ico_symm]

lemma ico_Binv (x : UnitAddCircle) : ico ((symT FormalABC.B)⁻¹ x) = bInv (ico x) := by
  obtain ⟨h0, h1⟩ := bInv_mem (ico_nonneg x) (ico_lt_one x).le
  have hlt : bInv (ico x) < 0 + 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · simpa using h
    · exfalso
      have := bFun_bInv (ico x); rw [h] at this
      rw [bFun_of_mem3 (by norm_num) le_rfl] at this
      linarith [ico_lt_one x]
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨bInv (ico x), h0, hlt⟩
  have hz : symT FormalABC.B z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.B z) = ico x
    rw [ico_B, ico_symm]
    exact bFun_bInv (ico x)
  rw [inv_apply_eq_of hz, ico_symm]

lemma ico_Cinv (x : UnitAddCircle) : ico ((symT FormalABC.C)⁻¹ x) = cInv (ico x) := by
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨cInv (ico x), cInv_mem ⟨ico_nonneg x, by simpa using ico_lt_one x⟩⟩
  have hz : symT FormalABC.C z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.C z) = ico x
    rw [ico_C, ico_symm]
    exact cFun_cInv ⟨ico_nonneg x, by simpa using ico_lt_one x⟩
  rw [inv_apply_eq_of hz, ico_symm]

end CannonFloydParry.S5

/-! Lemma 5.2, relations 1)–6), for the circle maps (generated by scripts/gen_relations.py). -/

namespace CannonFloydParry.S5

local notation "a" => symT FormalABC.A
local notation "b" => symT FormalABC.B
local notation "c" => symT FormalABC.C

set_option maxHeartbeats 4000000 in
lemma rel1T : (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹ = 1 := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_A, ico_B, ico_C, ico_Ainv, ico_Binv, ico_Cinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 4 : ℝ) with hq0 | hp0
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : bInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL2 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL3 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL4 : bFun ((2 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL5 : aFun ((2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL6 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL7 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL8 : bInv ((2 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL9 : aFun ((2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9] <;> ring1
  rcases lt_or_ge y (1 / 2 : ℝ) with hq1 | hp1
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : bInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL2 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL3 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL4 : bFun ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eL5 : aFun ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL6 : bFun ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL7 : aInv ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL8 : bInv ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [bInv_of_mem1] <;> first | ring1 | linarith
    have eL9 : aFun ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq2 | hp2
  · have eL0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL1 : bInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL3 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL4 : bFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL5 : aFun ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL6 : bFun ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL7 : aInv ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL8 : bInv ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem2] <;> first | ring1 | linarith
    have eL9 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9] <;> ring1
  rcases lt_or_ge y (13 / 16 : ℝ) with hq3 | hp3
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : bInv ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-5 / 2 : ℝ) := by rw [bInv_of_mem1] <;> first | ring1 | linarith
    have eL2 : aInv ((4 : ℝ) * y + (-5 / 2 : ℝ)) = (2 : ℝ) * y + (-3 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL3 : aInv ((2 : ℝ) * y + (-3 / 4 : ℝ)) = (1 : ℝ) * y + (1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL4 : bFun ((1 : ℝ) * y + (1 / 8 : ℝ)) = (2 : ℝ) * y + (-3 / 4 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    have eL5 : aFun ((2 : ℝ) * y + (-3 / 4 : ℝ)) = (4 : ℝ) * y + (-5 / 2 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL6 : bFun ((4 : ℝ) * y + (-5 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eL7 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL8 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
    have eL9 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq4 | hp4
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : bInv ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-7 / 8 : ℝ) := by rw [bInv_of_mem2] <;> first | ring1 | linarith
    have eL2 : aInv ((2 : ℝ) * y + (-7 / 8 : ℝ)) = (1 : ℝ) * y + (1 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL3 : aInv ((1 : ℝ) * y + (1 / 16 : ℝ)) = (1 / 2 : ℝ) * y + (17 / 32 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL4 : bFun ((1 / 2 : ℝ) * y + (17 / 32 : ℝ)) = (1 : ℝ) * y + (1 / 16 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    have eL5 : aFun ((1 : ℝ) * y + (1 / 16 : ℝ)) = (2 : ℝ) * y + (-7 / 8 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL6 : bFun ((2 : ℝ) * y + (-7 / 8 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL7 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL8 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
    have eL9 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9] <;> ring1
  have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL1 : bInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
  have eL2 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL3 : aInv ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL4 : bFun ((1 / 4 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eL5 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL6 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eL7 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL8 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
  have eL9 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9] <;> ring1

set_option maxHeartbeats 4000000 in
lemma rel2T : (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ = 1 := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_A, ico_B, ico_C, ico_Ainv, ico_Binv, ico_Cinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 4 : ℝ) with hq0 | hp0
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : aFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL2 : bInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL3 : aInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL4 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL5 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL6 : bFun ((2 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL7 : aFun ((2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL8 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL9 : bFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL10 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL11 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL12 : bInv ((2 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL13 : aFun ((2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13] <;> ring1
  rcases lt_or_ge y (1 / 2 : ℝ) with hq1 | hp1
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : aFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL2 : bInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL3 : aInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL4 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL5 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL6 : bFun ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eL7 : aFun ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL8 : aFun ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 4 : ℝ) * y + (1 / 16 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL9 : bFun ((1 / 4 : ℝ) * y + (1 / 16 : ℝ)) = (1 / 4 : ℝ) * y + (1 / 16 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL10 : aInv ((1 / 4 : ℝ) * y + (1 / 16 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL11 : aInv ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL12 : bInv ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [bInv_of_mem1] <;> first | ring1 | linarith
    have eL13 : aFun ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq2 | hp2
  · have eL0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL1 : aFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL2 : bInv ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL3 : aInv ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL4 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL5 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL6 : bFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL7 : aFun ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL8 : aFun ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 4 : ℝ) * y + (1 / 16 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL9 : bFun ((1 / 4 : ℝ) * y + (1 / 16 : ℝ)) = (1 / 4 : ℝ) * y + (1 / 16 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL10 : aInv ((1 / 4 : ℝ) * y + (1 / 16 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 8 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL11 : aInv ((1 / 2 : ℝ) * y + (1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL12 : bInv ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem2] <;> first | ring1 | linarith
    have eL13 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq3 | hp3
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL2 : bInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith
    have eL3 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL4 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL5 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL6 : bFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    have eL7 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL8 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL9 : bFun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL10 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL11 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL12 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
    have eL13 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13] <;> ring1
  rcases lt_or_ge y (29 / 32 : ℝ) with hq4 | hp4
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL2 : bInv ((4 : ℝ) * y + (-3 : ℝ)) = (8 : ℝ) * y + (-13 / 2 : ℝ) := by rw [bInv_of_mem1] <;> first | ring1 | linarith
    have eL3 : aInv ((8 : ℝ) * y + (-13 / 2 : ℝ)) = (4 : ℝ) * y + (-11 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL4 : aInv ((4 : ℝ) * y + (-11 / 4 : ℝ)) = (2 : ℝ) * y + (-7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL5 : aInv ((2 : ℝ) * y + (-7 / 8 : ℝ)) = (1 : ℝ) * y + (1 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL6 : bFun ((1 : ℝ) * y + (1 / 16 : ℝ)) = (2 : ℝ) * y + (-7 / 8 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    have eL7 : aFun ((2 : ℝ) * y + (-7 / 8 : ℝ)) = (4 : ℝ) * y + (-11 / 4 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL8 : aFun ((4 : ℝ) * y + (-11 / 4 : ℝ)) = (8 : ℝ) * y + (-13 / 2 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL9 : bFun ((8 : ℝ) * y + (-13 / 2 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eL10 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL11 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL12 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
    have eL13 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq5 | hp5
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL2 : bInv ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-23 / 8 : ℝ) := by rw [bInv_of_mem2] <;> first | ring1 | linarith
    have eL3 : aInv ((4 : ℝ) * y + (-23 / 8 : ℝ)) = (2 : ℝ) * y + (-15 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL4 : aInv ((2 : ℝ) * y + (-15 / 16 : ℝ)) = (1 : ℝ) * y + (1 / 32 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL5 : aInv ((1 : ℝ) * y + (1 / 32 : ℝ)) = (1 / 2 : ℝ) * y + (33 / 64 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL6 : bFun ((1 / 2 : ℝ) * y + (33 / 64 : ℝ)) = (1 : ℝ) * y + (1 / 32 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    have eL7 : aFun ((1 : ℝ) * y + (1 / 32 : ℝ)) = (2 : ℝ) * y + (-15 / 16 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL8 : aFun ((2 : ℝ) * y + (-15 / 16 : ℝ)) = (4 : ℝ) * y + (-23 / 8 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL9 : bFun ((4 : ℝ) * y + (-23 / 8 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL10 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL11 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL12 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
    have eL13 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13] <;> ring1
  have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL2 : bInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
  have eL3 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL4 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL5 : aInv ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL6 : bFun ((1 / 4 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eL7 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL8 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL9 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eL10 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL11 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL12 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith
  have eL13 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11, eL12, eL13] <;> ring1

set_option maxHeartbeats 4000000 in
lemma rel3T : c = b * (a⁻¹ * c * b) := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_A, ico_B, ico_C, ico_Ainv, ico_Binv, ico_Cinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : cFun (y) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eR1 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eR2 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eR3 : bFun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eR0, eR1, eR2, eR3] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : cFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eR1 : cFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR2 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eR3 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    rw [eL0, eR0, eR1, eR2, eR3] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : cFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eR1 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eR3 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    rw [eL0, eR0, eR1, eR2, eR3] <;> ring1
  have eL0 : cFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eR0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eR1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eR2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eR3 : bFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
  rw [eL0, eR0, eR1, eR2, eR3] <;> ring1

set_option maxHeartbeats 4000000 in
lemma rel4T : (a⁻¹ * c * b) * (a⁻¹ * b * a) = b * (a⁻¹ ^ 2 * c * b ^ 2) := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_A, ico_B, ico_C, ico_Ainv, ico_Binv, ico_Cinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : bFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL2 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eL3 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL4 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eL5 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eR1 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eR2 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eR3 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eR4 : aInv ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 8 : ℝ) * y + (15 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eR5 : bFun ((1 / 8 : ℝ) * y + (15 / 16 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL1 : bFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eL3 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eL4 : cFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eL5 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eR1 : bFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 8 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eR2 : cFun ((1 / 4 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR3 : aInv ((1 / 2 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eR4 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eR5 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL3 : bFun ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL4 : cFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eL5 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eR1 : bFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 16 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eR2 : cFun ((1 / 2 : ℝ) * y + (3 / 16 : ℝ)) = (1 : ℝ) * y + (-5 / 8 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR3 : aInv ((1 : ℝ) * y + (-5 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eR4 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eR5 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq3 | hp3
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL2 : aInv ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eL3 : bFun ((1 : ℝ) * y + (-1 / 16 : ℝ)) = (1 : ℝ) * y + (-3 / 16 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eL4 : cFun ((1 : ℝ) * y + (-3 / 16 : ℝ)) = (2 : ℝ) * y + (-11 / 8 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eL5 : aInv ((2 : ℝ) * y + (-11 / 8 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    have eR1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eR2 : cFun ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR3 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eR4 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eR5 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eL2 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eL3 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eL4 : cFun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eL5 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eR0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eR1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eR2 : cFun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eR3 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eR4 : aInv ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eR5 : bFun ((1 : ℝ) * y + (-1 / 16 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1

set_option maxHeartbeats 4000000 in
lemma rel5T : c * a = (a⁻¹ * c * b) ^ 2 := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_A, ico_B, ico_C, ico_Ainv, ico_Binv, ico_Cinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : cFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eR1 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eR2 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    have eR3 : bFun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
    have eR4 : cFun ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
    have eR5 : aInv ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith
    have eL1 : cFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (5 / 8 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eR1 : cFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR2 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    have eR3 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith
    have eR4 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eR5 : aInv ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (5 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
    have eL1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
    have eR1 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
    have eR3 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith
    have eR4 : cFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (2 : ℝ) * y + (-3 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eR5 : aInv ((2 : ℝ) * y + (-3 / 2 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith
    rw [eL0, eL1, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith
  have eL1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eR0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith
  have eR1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eR2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith
  have eR3 : bFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith
  have eR4 : cFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (2 : ℝ) * y + (-3 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
  have eR5 : aInv ((2 : ℝ) * y + (-3 / 2 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith
  rw [eL0, eL1, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1

set_option maxHeartbeats 4000000 in
lemma rel6T : c ^ 3 = 1 := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_A, ico_B, ico_C, ico_Ainv, ico_Binv, ico_Cinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : cFun (y) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eL1 : cFun ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
    have eL2 : cFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : cFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
    have eL1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
    have eL2 : cFun ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
    rw [eL0, eL1, eL2] <;> ring1
  have eL0 : cFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith
  have eL1 : cFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (2 : ℝ) * y + (-3 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith
  have eL2 : cFun ((2 : ℝ) * y + (-3 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith
  rw [eL0, eL1, eL2] <;> ring1

end CannonFloydParry.S5

/-! Lifts of elements of `T` to the line, and the closure theorem (the first milestone): the
maps satisfying `IsThompsonCircle` form a group. -/

namespace CannonFloydParry.S5

/-! ### Dyadic arithmetic -/

lemma isDyadic_int (k : ℤ) : IsDyadic (k : ℝ) := ⟨k, 0, by simp⟩

lemma dy_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨n, l, rfl⟩ := hy
  refine ⟨m * 2 ^ l + n * 2 ^ k, k + l, ?_⟩
  push_cast
  field_simp
  ring

lemma dy_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma dy_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  simpa [sub_eq_add_neg] using dy_add hx (dy_neg hy)

lemma dy_zpow {x : ℝ} (hx : IsDyadic x) (n : ℤ) : IsDyadic ((2 : ℝ) ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  rcases n with n | n
  · refine ⟨m * 2 ^ n, k, ?_⟩
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    push_cast
    ring
  · refine ⟨m, k + (n + 1), ?_⟩
    rw [zpow_negSucc, pow_add]
    field_simp
    ring

lemma dy_fract {x : ℝ} (hx : IsDyadic x) : IsDyadic (Int.fract x) := by
  rw [Int.fract]; exact dy_sub hx (isDyadic_int _)

/-! ### Good lifts -/

/-- `L` is affine with slope a power of `2` on every closed interval whose interior avoids the
integer translates of `B`. -/
def IsPL (L : ℝ ≃o ℝ) (B : Finset ℝ) : Prop :=
  ∀ x y : ℝ, x < y → (∀ t ∈ Set.Ioo x y, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k) →
    ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, L z = 2 ^ n * z + c

structure GoodLift (L : ℝ ≃o ℝ) : Prop where
  per : ∀ x, L (x + 1) = L x + 1
  dy : ∀ x, IsDyadic x → IsDyadic (L x)
  pl : ∃ B : Finset ℝ, (∀ b ∈ B, IsDyadic b) ∧ IsPL L B

lemma isThompsonCircle_iff {f : Equiv.Perm UnitAddCircle} :
    IsThompsonCircle f ↔ ∃ L : ℝ ≃o ℝ, GoodLift L ∧ ∀ x : ℝ, f (x : UnitAddCircle) = ((L x : ℝ) : UnitAddCircle) := by
  constructor
  · rintro ⟨L, hper, hcov, hdy, B, hB, hpl⟩
    exact ⟨L, ⟨hper, hdy, B, hB, hpl⟩, hcov⟩
  · rintro ⟨L, ⟨hper, hdy, B, hB, hpl⟩, hcov⟩
    exact ⟨L, hper, hcov, hdy, B, hB, hpl⟩

namespace GoodLift
variable {L : ℝ ≃o ℝ}

lemma per_nat (hL : GoodLift L) (x : ℝ) (n : ℕ) : L (x + n) = L x + n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, hL.per, ih]; ring

lemma per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L (x + k) = L x + k := by
  rcases k with n | n
  · simpa using hL.per_nat x n
  · have hc : ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by rw [Int.cast_negSucc]; push_cast; ring
    have := hL.per_nat (x + ((Int.negSucc n : ℤ) : ℝ)) (n + 1)
    rw [hc] at this ⊢
    push_cast at this
    rw [show x + -((n : ℝ) + 1) + ((n : ℝ) + 1) = x by ring] at this
    linarith

lemma symm_per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L.symm (x + k) = L.symm x + k := by
  apply L.injective
  rw [hL.per_int, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]

/-- The key fact: the inverse of a good lift maps dyadic rationals to dyadic rationals. -/
lemma symm_dy (hL : GoodLift L) (w : ℝ) (hw : IsDyadic w) : IsDyadic (L.symm w) := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  set z := L.symm w
  let S : Finset ℝ := insert ((⌊z⌋ : ℤ) : ℝ) (B.image fun b => b + ⌊z - b⌋)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  set x := S.max' hS
  have hxS : x ∈ S := S.max'_mem hS
  have hle : ∀ s ∈ S, s ≤ z := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact Int.floor_le z
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hs
      linarith [Int.floor_le (z - b)]
  have hxz : x ≤ z := hle x hxS
  have hxdy : IsDyadic x := by
    rcases Finset.mem_insert.1 hxS with h | h
    · rw [h]; exact isDyadic_int _
    · obtain ⟨b, hb, h⟩ := Finset.mem_image.1 h
      rw [← h]; exact dy_add (hB b hb) (isDyadic_int _)
  rcases eq_or_lt_of_le hxz with h | h
  · rw [← h]; exact hxdy
  have havoid : ∀ t ∈ Set.Ioo x z, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
    rintro t ⟨ht1, ht2⟩ b hb k rfl
    have hk : k ≤ ⌊z - b⌋ := Int.le_floor.2 (by linarith)
    have : b + ⌊z - b⌋ ≤ x := S.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb))
    have : (k : ℝ) ≤ ⌊z - b⌋ := by exact_mod_cast hk
    linarith
  obtain ⟨n, c, hc⟩ := hpl x z h havoid
  have hcx := hc x ⟨le_rfl, hxz⟩
  have hcz := hc z ⟨hxz, le_rfl⟩
  have hcdy : IsDyadic c := by
    have : c = L x - 2 ^ n * x := by linarith
    rw [this]; exact dy_sub (hL.dy x hxdy) (dy_zpow hxdy n)
  have hzw : L z = w := OrderIso.apply_symm_apply L w
  have : z = 2 ^ (-n) * (w - c) := by
    rw [← hzw, hcz, zpow_neg]
    field_simp
    ring
  rw [this]
  exact dy_zpow (dy_sub hw hcdy) _

lemma symm (hL : GoodLift L) : GoodLift L.symm := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  refine ⟨fun x => by simpa using hL.symm_per_int x 1, hL.symm_dy, B.image (fun b => Int.fract (L b)), ?_, ?_⟩
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    exact dy_fract (hL.dy b (hB b hb))
  · intro x y hxy havoid
    have hxy' : L.symm x < L.symm y := L.symm.strictMono hxy
    have havoid' : ∀ t ∈ Set.Ioo (L.symm x) (L.symm y), ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
      rintro t ⟨ht1, ht2⟩ b hb k rfl
      refine havoid (L (b + k)) ⟨?_, ?_⟩ (Int.fract (L b)) (Finset.mem_image_of_mem _ hb) (⌊L b⌋ + k) ?_
      · have := L.strictMono ht1; rwa [OrderIso.apply_symm_apply] at this
      · have := L.strictMono ht2; rwa [OrderIso.apply_symm_apply] at this
      · rw [hL.per_int]; push_cast; rw [Int.fract]; ring
    obtain ⟨n, c, hc⟩ := hpl _ _ hxy' havoid'
    refine ⟨-n, -(2 ^ (-n) * c), fun z hz => ?_⟩
    have hs : L.symm z ∈ Set.Icc (L.symm x) (L.symm y) :=
      ⟨L.symm.monotone hz.1, L.symm.monotone hz.2⟩
    have := hc _ hs
    rw [OrderIso.apply_symm_apply] at this
    rw [zpow_neg]
    field_simp
    linarith

end GoodLift

/-! ### The closure theorem -/

end CannonFloydParry.S5

/-! Example 5.1 (the second milestone): elements of `F` induce elements of `T`, and `C ∈ T`.
Both lifts are periodic extensions `x ↦ ℓ(fract x) + ⌊x⌋`. -/

namespace CannonFloydParry.S5

lemma ico_coe (x : ℝ) : ico (x : UnitAddCircle) = Int.fract x := by
  simp [ico, AddCircle.coe_equivIco_mk_apply]

lemma circle_ext {u v : UnitAddCircle} (h : ico u = ico v) : u = v :=
  (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)

/-! ### Periodic extensions -/

noncomputable def perExt (ℓ : ℝ → ℝ) (x : ℝ) : ℝ := ℓ (Int.fract x) + ⌊x⌋

structure PerData (ℓ : ℝ → ℝ) : Prop where
  mono : StrictMonoOn ℓ (Set.Icc 0 1)
  one : ℓ 1 = ℓ 0 + 1
  surj : ∀ v ∈ Set.Icc (ℓ 0) (ℓ 0 + 1), ∃ u ∈ Set.Icc (0 : ℝ) 1, ℓ u = v

namespace PerData
variable {ℓ : ℝ → ℝ} (h : PerData ℓ)
include h

lemma fract_mem (x : ℝ) : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

lemma lt_top (x : ℝ) : ℓ (Int.fract x) < ℓ 0 + 1 := by
  rw [← h.one]; exact h.mono (h.fract_mem x) ⟨zero_le_one, le_rfl⟩ (Int.fract_lt_one x)

lemma bot_le (x : ℝ) : ℓ 0 ≤ ℓ (Int.fract x) :=
  h.mono.monotoneOn ⟨le_rfl, zero_le_one⟩ (h.fract_mem x) (Int.fract_nonneg x)

lemma strictMono : StrictMono (perExt ℓ) := by
  intro x y hxy
  unfold perExt
  rcases eq_or_lt_of_le (Int.floor_mono hxy.le) with he | hl
  · have : Int.fract x < Int.fract y := by
      unfold Int.fract; rw [he]; linarith
    rw [he]
    have := h.mono (h.fract_mem x) (h.fract_mem y) this
    linarith
  · have hk : (⌊x⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast hl
    linarith [h.lt_top x, h.bot_le y]

lemma surjective : Function.Surjective (perExt ℓ) := by
  intro v
  set k := ⌊v - ℓ 0⌋
  have hk1 : (k : ℝ) ≤ v - ℓ 0 := Int.floor_le _
  have hk2 : v - ℓ 0 < k + 1 := Int.lt_floor_add_one _
  obtain ⟨u, hu, hlu⟩ := h.surj (v - k) ⟨by linarith, by linarith⟩
  have hu1 : u < 1 := by
    rcases eq_or_lt_of_le hu.2 with rfl | h1
    · rw [h.one] at hlu; linarith
    · exact h1
  refine ⟨u + k, ?_⟩
  unfold perExt
  rw [Int.fract_add_intCast, Int.fract_eq_self.2 ⟨hu.1, hu1⟩, Int.floor_add_intCast,
    Int.floor_eq_zero_iff.2 ⟨hu.1, hu1⟩]
  push_cast
  linarith

/-- The lift as an order isomorphism of the line. -/
noncomputable def lift : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective _ h.strictMono h.surjective

@[simp] lemma lift_apply (x : ℝ) : h.lift x = perExt ℓ x := rfl

lemma per (x : ℝ) : h.lift (x + 1) = h.lift x + 1 := by
  simp only [lift_apply, perExt]
  rw [Int.fract_add_one, Int.floor_add_one]; push_cast; ring

end PerData

/-! ### Elements of `F` -/

/-! ### The map `C` -/

end CannonFloydParry.S5

/-! Lemma 5.2: `A`, `B`, `C` generate `T` and satisfy relations 1)–6) (CFP pp. 234–235). -/

namespace CannonFloydParry.S5

theorem closure_range_symT_eq_T_and_relations' :
    Subgroup.closure (Set.range symT) = T ∧
      let a := symT FormalABC.A
      let b := symT FormalABC.B
      let c := symT FormalABC.C
      (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹ = 1 ∧
      (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ = 1 ∧
      c = b * (a⁻¹ * c * b) ∧
      (a⁻¹ * c * b) * (a⁻¹ * b * a) = b * (a⁻¹ ^ 2 * c * b ^ 2) ∧
      c * a = (a⁻¹ * c * b) ^ 2 ∧
      c ^ 3 = 1 := by
  refine ⟨?_, ⟨rel1T, rel2T, rel3T, rel4T, rel5T, rel6T⟩⟩
  set H := Subgroup.closure (Set.range symT)
  have hAF : mapA ∈ F := closure_mapA_mapB_eq_F ▸ Subgroup.subset_closure (by simp)
  have hBF : mapB ∈ F := closure_mapA_mapB_eq_F ▸ Subgroup.subset_closure (by simp)
  have hmemT : ∀ s, symT s ∈ T := by
    intro s
    cases s
    · exact toCircle_mem_T_and_mapC_mem_T.1 _ hAF
    · exact toCircle_mem_T_and_mapC_mem_T.1 _ hBF
    · exact toCircle_mem_T_and_mapC_mem_T.2
  refine le_antisymm ((Subgroup.closure_le T).2 (by rintro _ ⟨s, rfl⟩; exact hmemT s)) ?_
  have hF : ∀ g ∈ F, toCircle g ∈ H := by
    intro g hg
    rw [← closure_mapA_mapB_eq_F] at hg
    have hle : (Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI))).map toCircleHom ≤ H := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · exact ⟨FormalABC.A, rfl⟩
      · exact ⟨FormalABC.B, rfl⟩
    exact hle ⟨g, hg, rfl⟩
  intro f hf
  obtain ⟨L, hL, hcov⟩ := isThompsonCircle_iff.1 (mem_T_iff_isThompsonCircle.1 hf)
  set x0 := Int.fract (L 0)
  have hx0nn : 0 ≤ x0 := Int.fract_nonneg _
  have hx0lt : x0 < 1 := Int.fract_lt_one _
  have hf0 : f 0 = ((x0 : ℝ) : UnitAddCircle) := by
    apply circle_ext
    rw [show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) from rfl, hcov, ico_coe, ico_coe,
      Int.fract_eq_self.2 ⟨hx0nn, hx0lt⟩]
  by_cases hx0 : x0 = 0
  · have : f 0 = 0 := by rw [hf0, hx0]; rfl
    obtain ⟨g, hg, rfl⟩ := exists_toCircle_eq_of_mem_T_of_apply_zero hf this
    exact hF g hg
  have hx0pos : 0 < x0 := lt_of_le_of_ne hx0nn (Ne.symm hx0)
  have hx0dy : IsDyadic x0 := dy_fract (hL.dy 0 ⟨0, 0, by simp⟩)
  let xs : Fin 3 → UI := ![⟨0, zero_mem_UI⟩, ⟨x0, hx0nn, hx0lt.le⟩, ⟨1, one_mem_UI⟩]
  let ys : Fin 3 → UI := ![⟨0, zero_mem_UI⟩, ⟨3/4, by norm_num, by norm_num⟩, ⟨1, one_mem_UI⟩]
  have hxs : StrictMono xs := by
    refine Fin.strictMono_iff_lt_succ.2 (fun i => ?_)
    fin_cases i
    · show (0 : ℝ) < x0; exact hx0pos
    · show x0 < (1 : ℝ); exact hx0lt
  have hys : StrictMono ys := by
    refine Fin.strictMono_iff_lt_succ.2 (fun i => ?_)
    fin_cases i
    · show (0 : ℝ) < 3/4; norm_num
    · show (3/4 : ℝ) < 1; norm_num
  obtain ⟨h, hh, hmap⟩ := exists_mem_F_map_partition xs ys hxs hys rfl rfl rfl rfl
    (by intro i; fin_cases i
        · show IsDyadic (0 : ℝ); exact ⟨0, 0, by norm_num⟩
        · exact hx0dy
        · show IsDyadic (1 : ℝ); exact ⟨1, 0, by norm_num⟩)
    (by intro i; fin_cases i
        · show IsDyadic (0 : ℝ); exact ⟨0, 0, by norm_num⟩
        · show IsDyadic (3/4 : ℝ); exact ⟨3, 2, by norm_num⟩
        · show IsDyadic (1 : ℝ); exact ⟨1, 0, by norm_num⟩)
  have hh1 : ((h ⟨x0, hx0nn, hx0lt.le⟩ : UI) : ℝ) = 3/4 := congrArg Subtype.val (hmap 1)
  set g := (symT FormalABC.C)⁻¹ * toCircle h * f
  have hgT : g ∈ T :=
    T.mul_mem (T.mul_mem (T.inv_mem (hmemT _)) (toCircle_mem_T_and_mapC_mem_T.1 h hh)) hf
  have hg0 : g 0 = 0 := by
    apply circle_ext
    simp only [g, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hf0, ico_Cinv, ico_toCircle]
    have e : (⟨ico ((x0 : ℝ) : UnitAddCircle), ico_nonneg _, (ico_lt_one _).le⟩ : UI) =
        ⟨x0, hx0nn, hx0lt.le⟩ := Subtype.ext (by
          show ico ((x0 : ℝ) : UnitAddCircle) = x0
          rw [ico_coe, Int.fract_eq_self.2 ⟨hx0nn, hx0lt⟩])
    rw [e, hh1, cInv_of_mem3 (by norm_num), show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) from rfl,
      ico_coe]
    norm_num
  obtain ⟨g', hg', hgg'⟩ := exists_toCircle_eq_of_mem_T_of_apply_zero hgT hg0
  have hgH : g ∈ H := hgg' ▸ hF g' hg'
  have hfg : f = (toCircle h)⁻¹ * symT FormalABC.C * g := by simp only [g]; group
  rw [hfg]
  exact H.mul_mem (H.mul_mem (H.inv_mem (hF h hh)) (Subgroup.subset_closure ⟨FormalABC.C, rfl⟩)) hgH

end CannonFloydParry.S5

open CannonFloydParry

theorem solution :
    Subgroup.closure (Set.range symT) = T ∧
      let a := symT FormalABC.A
      let b := symT FormalABC.B
      let c := symT FormalABC.C
      (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹ = 1 ∧
      (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ = 1 ∧
      c = b * (a⁻¹ * c * b) ∧
      (a⁻¹ * c * b) * (a⁻¹ * b * a) = b * (a⁻¹ ^ 2 * c * b ^ 2) ∧
      c * a = (a⁻¹ * c * b) ^ 2 ∧
      c ^ 3 = 1 :=
  CannonFloydParry.S5.closure_range_symT_eq_T_and_relations'
