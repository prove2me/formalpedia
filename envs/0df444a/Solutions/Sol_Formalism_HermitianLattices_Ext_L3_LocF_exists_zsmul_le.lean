-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.exists_zsmul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:53.826381+00:00
-- url     : https://prove2.me/submissions/d354ce1d-7a4c-42cc-abbc-0421af8d70c6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_mult


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  obtain ⟨S, hS⟩ := hA.fg
  choose n hn hnx using fun x : V => Formalism.HermitianLatticesTheory.traceReal_mult B hB x
  refine ⟨∏ x ∈ S, n x, Finset.prod_ne_zero_iff.mpr fun x _ => hn x, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hy
    rw [hm, mul_comm, mul_smul]
    exact zsmul_mem (hnx y) m
  | zero => rw [smul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact B.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact B.smul_mem a hy
end Formalism.HermitianLattices.Ext.L3.LocF
