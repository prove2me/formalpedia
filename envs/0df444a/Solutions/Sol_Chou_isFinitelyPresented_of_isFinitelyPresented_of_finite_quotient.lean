-- Prove2me | solution 1 for Chou.isFinitelyPresented_of_isFinitelyPresented_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-20T09:27:17.163128+00:00
-- url     : https://prove2.me/submissions/621b42d4-409f-4b27-86d7-0fba55515344

import Theorems.Thm_GroupFiniteness_isFinitelyPresented_of_extension
import Mathlib

namespace Chou
namespace Lib

/-- Chou, p. 400: "`C` is finitely presented since it is the extension of the finitely presented
group `C₁` by the finite group `C/C₁`."  A corollary of P. Hall's theorem on extensions, since a
finite group is finitely presented. -/
theorem isFinitelyPresented_of_isFinitelyPresented_of_finite_quotient' {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [Group.IsFinitelyPresented N] [Finite (G ⧸ N)] :
    Group.IsFinitelyPresented G :=
  GroupFiniteness.isFinitelyPresented_of_extension N

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsFinitelyPresented N] [Finite (G ⧸ N)] : Group.IsFinitelyPresented G :=
  Chou.Lib.isFinitelyPresented_of_isFinitelyPresented_of_finite_quotient' N
