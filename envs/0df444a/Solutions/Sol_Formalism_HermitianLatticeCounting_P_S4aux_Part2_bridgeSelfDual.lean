-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.bridgeSelfDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:57.851581+00:00
-- url     : https://prove2.me/submissions/e9eb5de3-14c0-43fa-9690-fdbafaf7d0bd

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution : BridgeSelfDual := by
  intro E _ _ _ V _ _ h O abelian₂ O' Lam' _ _ _ _ h' io j hM hh n b hb hperf hdual

  have hbi : ∀ i, b i ∈ abelian₂ := fun i => (hb _).mpr fun k => by
    rw [b.repr_self, Finsupp.single_apply]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  choose b' hb' using fun i => (hM.j_range _).mp (hbi i)
  have hco : ∀ v : Lam', ∀ i, ∃ a, io a = b.repr (j v) i := fun v i =>
    (hM.io_range _).mp ((hb _).mp ((hM.j_range _).mpr ⟨v, rfl⟩) i)
  choose co hcoe using hco
  have jsum : ∀ c : Fin n → O', j (∑ i, c i • b' i) = ∑ i, io (c i) • b i := by
    intro c; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hM.j_smul, hb']
  have hexp : ∀ v : Lam', v = ∑ i, co v i • b' i := by
    intro v
    apply hM.j_inj
    rw [jsum]
    conv_lhs => rw [← b.sum_repr (j v)]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoe]
  have hind : ∀ c : Fin n → O', (∑ i, c i • b' i) = 0 → ∀ i, c i = 0 := by
    intro c hc i
    have h0 : ∑ i, io (c i) • b i = 0 := by rw [← jsum, hc, map_zero]
    have := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun i => io (c i)) h0 i
    exact hM.io_inj (by rw [this, map_zero])
  have hli : LinearIndependent O' b' := Fintype.linearIndependent_iff.mpr hind
  have hsp : ⊤ ≤ Submodule.span O' (Set.range b') := by
    intro v _
    rw [hexp v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B' : Module.Basis (Fin n) O' Lam' := Module.Basis.mk hli hsp
  have : Nontrivial O' := ⟨⟨0, 1, fun h01 => by
    have := congrArg io h01
    rw [map_zero, map_one] at this
    exact zero_ne_one this⟩⟩
  refine ⟨⟨?_, ?_⟩, Module.Free.of_basis B', Module.Finite.of_basis B', ?_⟩
  · intro v w
    apply hM.io_inj
    rw [← hM.form, hh, hM.form, hM.io_star]
  · intro φ
    obtain ⟨v, hv⟩ := hperf (b.constr E (fun i => io (φ (b' i))))
    have key : ∀ x : Lam', io (φ x) = h (j x) v := by
      intro x
      rw [← hv]
      conv_lhs => rw [hexp x]
      conv_rhs => rw [hexp x, jsum]
      simp [map_sum]
    have hvL : v ∈ abelian₂ := hdual v fun w hw => by
      obtain ⟨x, rfl⟩ := (hM.j_range _).mp hw
      rw [← key]; exact (hM.io_range _).mpr ⟨_, rfl⟩
    obtain ⟨w, rfl⟩ := (hM.j_range _).mp hvL
    exact ⟨w, fun x => hM.io_inj (by rw [key, hM.form])⟩
  · rw [Module.finrank_eq_card_basis B']; simp
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
