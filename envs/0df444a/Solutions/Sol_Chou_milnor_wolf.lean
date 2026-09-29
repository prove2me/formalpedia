-- Prove2me | solution 1 for Chou.milnor_wolf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-20T16:59:25.20098+00:00
-- url     : https://prove2.me/submissions/e8aa5ed0-abe4-4cd5-86d2-42e11b980ae4

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Theorems.Thm_Wolf_growth_dichotomy_of_isSolvable_of_fg
import Theorems.Thm_Chou_hasExponentialGrowth_iff_forall
import Mathlib

/-!
# Chou's citation of Milnor–Wolf (p. 399)

Chou cites Milnor and Wolf for the statement that a finitely generated solvable group which is
exponentially bounded is almost nilpotent.  That is the contrapositive of the second alternative
of Wolf's Theorem 4.8: a finitely generated solvable group with no nilpotent subgroup of finite
index has exponential growth.  The two predicates quantify over *some* finite generating set, so
turning one into the negation of the other needs Wolf's observation, formalized here as
`Chou.hasExponentialGrowth_iff_forall`, that exponential growth does not depend on which finite
generating set is used.
-/

namespace Chou
namespace Lib

/-- **Milnor–Wolf** in the form Chou uses it (p. 399): a finitely generated solvable group which
is exponentially bounded is almost nilpotent. -/
theorem milnor_wolf' {G : Type*} [Group G] [Group.FG G] [Group.IsSolvable G]
    (h : Chou.IsExponentiallyBounded G) : Group.IsVirtuallyNilpotent G := by
  by_contra hno
  have hexp : Chou.HasExponentialGrowth G :=
    (Wolf.growth_dichotomy_of_isSolvable_of_fg (Γ := G)).2 hno
  obtain ⟨S, hS, hbd⟩ := h
  obtain ⟨c, hc, hcn⟩ := (_root_.Chou.hasExponentialGrowth_iff_forall (G := G)).1 hexp S hS
  set d : ℝ := (1 + c) / 2 with hd
  have hd1 : 1 < d := by rw [hd]; linarith
  have hdc : d < c := by rw [hd]; linarith
  obtain ⟨N, hN⟩ := hbd d hd1
  have hn : max N 1 ≥ N := le_max_left _ _
  have h1 : (1 : ℕ) ≤ max N 1 := le_max_right _ _
  have hle := hN (max N 1) hn
  have hge := hcn (max N 1)
  have hlt : d ^ (max N 1) < c ^ (max N 1) :=
    pow_lt_pow_left₀ hdc (by linarith) (by omega)
  linarith

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] [Group.FG G] [Group.IsSolvable G] (h : IsExponentiallyBounded G) :
    Group.IsVirtuallyNilpotent G :=
  Chou.Lib.milnor_wolf' h
