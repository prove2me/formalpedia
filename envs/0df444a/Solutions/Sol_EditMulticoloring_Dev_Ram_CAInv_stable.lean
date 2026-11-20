-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.CAInv.stable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:04.866936+00:00
-- url     : https://prove2.me/submissions/d60fbeba-fd70-4246-b841-f1f329a6826a

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamColor4
/-!
# `colorsAll`: the colour of `x` and of each of its neighbours (q379, Part G)

`colorsAll q t cfg1 cfg2 g X2 XA DG CLA`: `colorOf` (block `g .. g+50`, enumerator `cfg2`) on `x`
(result `g+51`), then the enumerator `cfg1` over `visits (2t) x`; for every visited `w` of length
`|x|` other than `x` (in visit order, duplicates kept: the list `nbrList t x`) it copies `w`
into `cfg2.buf (2t)`, runs `colorOf` and stores the colour at `CLA[J]`, `J := J + 1` (`g+52`).
Own registers `g+51 .. g+67`; `cfg2.r0 ≥ g + 68`, `cfg1.r0` above the registers of `cfg2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The program -/

theorem CAInv.stable_oai {q : ℕ} {t : ℕ} {cfg1 cfg2 : EnumCfg} {g XA DG CLA p Q K : ℕ} {x : Word q}
    {st0 : HS} (h1r : g + 68 ≤ cfg1.r0) (hCLA : CLA < cfg1.a0)
    {l : List (Word q)} {st st' : HS} (h : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st)
    (hA : cfg1.Agree (2 * t) st st') : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have nR : ∀ r, r < cfg1.r0 → ¬ cfg1.ownsReg (2 * t) r := fun r hr h => by
    simp only [EnumCfg.ownsReg] at h; omega
  have nA : ¬ cfg1.ownsArr (2 * t) CLA := fun h => by simp only [EnumCfg.ownsArr] at h; omega
  exact ⟨(hA.1 _ (nR _ (by omega))).trans h1, h2,
    fun m hm P hP hK => (hA.2.1 _ _ nA).trans (h3 m hm P hP hK),
    fun r hr hn => (hA.1 _ hn).trans (h4 r hr hn),
    fun y i a b c d e => (hA.2.1 _ _ e).trans (h5 y i a b c d e),
    hA.2.2.1.trans h6, hA.2.2.2.trans h7⟩


end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.CAInv.stable_oai := @EditMulticoloring.Dev.Ram.CAInv.stable_oai
