-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EnumCfg.lev_zero_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:30.430806+00:00
-- url     : https://prove2.me/submissions/3a5ec2ff-7a4f-4969-8e7a-f15814be0cb5

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_visitC_spec

section
-- module Solutions.EditMulticoloring.RamEnum
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator (q379, Part L)

`enumScripts q s cfg body` runs `body` once per element of `visits s x` (in list order), each
time with the visited word in array `cfg.vis` (offset 0) and its length in register `cfg.VL`.
Main theorem: `enumScripts_spec` (RamEnum3.lean); level induction in RamEnum2.lean.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The visit list -/

theorem visits_zero {q : ℕ} (x : Word q) : visits 0 x = [x] := by
  simp [visits, scripts]

/-! ## Configuration -/

namespace EnumCfg
variable (c : EnumCfg)

theorem Fr.agree {s w Y : ℕ} {st st' : HS} (h : c.Fr w Y st st') (hw : c.ownsReg s w)
    (hY : c.ownsArr s Y) : c.Agree s st st' := by
  refine ⟨fun r hr => h.1 r ?_ ?_, fun y i hy => h.2.1 y i ?_, h.2.2.1, h.2.2.2⟩
  · simp only [ownsReg, not_and, not_le] at hr; omega
  · rintro rfl; exact hr hw
  · rintro rfl; exact hy hY

/-! ## Code -/

end EnumCfg

/-! ## Specs of the pieces -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEnum2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# The scripts enumerator, part 2: the three edit phases (q379, Part L)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Membership in the visit list -/

/-! ## Positions in the visit list -/

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

theorem ownsReg_of {s r : ℕ} (h1 : c.r0 ≤ r) (h2 : r ≤ c.r0 + (18 + 3 * s)) : c.ownsReg s r :=
  ⟨h1, h2⟩

theorem ownsArr_of {s y : ℕ} (h1 : c.a0 ≤ y) (h2 : y ≤ c.a0 + 1 + s) : c.ownsArr s y :=
  ⟨h1, h2⟩

section Phases
variable {q : ℕ} {α : Type*} (s L : ℕ) (body : Cmd) (Inv : α → HS → Prop) (f : α → Word q → α)
  (cb : ℕ) (Ok : α → Word q → Prop)

theorem lev_zero_spec_oai (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    (hbody : ∀ a st (w : Word q), Inv a st → Ok a w → st.regs c.VL = w.length →
      WordAt st c.vis 0 w →
      Inv (f a w) (body.exec inp st) ∧ c.BodyFrame s st (body.exec inp st) ∧
      body.cost inp B st ≤ cb) :
    c.IHk inp B s L body Inv f cb Ok 0 := by
  intro x a st hxL hok hInv hlen hx
  obtain ⟨v1, v2, v3, v4⟩ := c.visitC_spec inp B 0 x st hlen hx (c.enumM q L s)
    (by simp only [enumM]; omega)
  have hInv1 := hstable _ _ _ hInv (Fr.agree c v3 (c.ownsReg_of (by simp <;> omega) (by simp <;> omega))
    (c.ownsArr_of (by simp <;> omega) (by simp <;> omega)))
  obtain ⟨b1, b2, b3⟩ := hbody a _ x hInv1
    (by simpa [visits_zero] using hok 0 (by simp [visits_zero])) v1 v2
  have hex : (c.lev q body 0).exec inp st = body.exec inp ((c.visitC 0).exec inp st) := rfl
  rw [hex, visits_zero]
  refine ⟨b1, ⟨fun r h1 h2 => ?_, fun y j h1 h2 => ?_⟩, ?_⟩
  · rw [b2.1 r (c.ownsReg_of (by simp at h1 ⊢ <;> omega) (by simp at h2 ⊢ <;> omega))
      (by simp at h1 ⊢ <;> omega)]
    exact v3.1 r (Or.inr (by simp at h1 ⊢ <;> omega)) (by simp at h1 ⊢ <;> omega)
  · rw [b2.2 y j (c.ownsArr_of (by simp at h1 ⊢ <;> omega) (by simp at h2 ⊢ <;> omega))
      (by simp at h1 ⊢ <;> omega)]
    exact v3.2.1 y j (by simp at h1 ⊢ <;> omega)
  · have hc : (c.lev q body 0).cost inp B st =
        (c.visitC 0).cost inp B st + body.cost inp B ((c.visitC 0).exec inp st) := rfl
    rw [hc]
    simp only [List.length_singleton, one_mul, enumE]
    have : (7 * x.length + 10) * kappa B (RAM.bits (c.enumM q L s)) ≤
        100 * (q + 1) * (L + s + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s)) := by
      apply Nat.mul_le_mul_right
      nlinarith [Nat.zero_le (q * (L + s + 2) ^ 2)]
    omega

end Phases

end EnumCfg

end EditMulticoloring.Dev.Ram
end

theorem solution.{u_1} : type_of% @EditMulticoloring.Dev.Ram.EnumCfg.lev_zero_spec_oai.{u_1} := @EditMulticoloring.Dev.Ram.EnumCfg.lev_zero_spec_oai.{u_1}
