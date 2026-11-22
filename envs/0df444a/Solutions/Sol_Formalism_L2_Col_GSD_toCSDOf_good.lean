-- Prove2me | solution 1 for Formalism.L2.Col.GSD.toCSDOf_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:10.200424+00:00
-- url     : https://prove2.me/submissions/ed79fd24-2c30-4408-8c48-014fe25ea465

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
open Formalism.L2.Col.GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution {n : ℕ} (G : S.Good n) (s : S.Sec) : (S.toCSDOf G.ok s).Good n where
  symm := G.symm
  nondeg := G.nondeg
  inv := fun c γ x y => G.ok.inv ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) x y
  nab_lat := fun c => G.nab_lat (s.rep c)
  del_le := fun c => G.del_le (s.rep c)
  del_stable := by
    intro c γ y hy
    have h1 := G.ok.del_smul ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) (s.rep c)
    have h2 : ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) • s.rep c = s.rep c :=
      (γ : MulAction.stabilizer S.G (s.rep c)).2
    rw [h2] at h1
    show S.ρ ((γ : MulAction.stabilizer S.G (s.rep c)) : S.G) y ∈ S.Del (s.rep c)
    rw [h1]
    exact Submodule.mem_map_of_mem hy
  s_pos := G.s_pos
  dual_le := fun c => G.dual_le (s.rep c)
  del_dual := fun c => G.del_dual (s.rep c)
end Formalism.L2.Col.GSD
