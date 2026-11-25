-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallSum.ballCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:02.272217+00:00
-- url     : https://prove2.me/submissions/27c3c86e-b0b0-43bd-9a80-9216db609b37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IntegralOfMemGenus
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallSum_exists_mem_boxSet
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_boxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_finite_rep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallSum
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} (hT : 0 ≤ T) :
    ballCount h M T =
      1 + ∑ n ∈ (finite_boxSet hK hF T).toFinset, repCount h M (algebraMap F K (n : F)) := by
  classical
  let Fn : 𝓞 F → Finset V := fun n => (StabilizerLattices.finite_rep hd hM (algebraMap F K (n : F))).toFinset
  have hset : {x : V | x ∈ M ∧ ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T} =
      ↑(insert 0 ((finite_boxSet hK hF T).toFinset.biUnion Fn)) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn]
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · obtain ⟨n, hn, he⟩ := exists_mem_boxSet hF hs hd hMi hx hx0 hxT
        exact Or.inr ⟨n, hn, hx, he⟩
    · rintro (rfl | ⟨n, hn, hx, he⟩)
      · exact ⟨M.zero_mem, fun φ => by simp [hT]⟩
      · exact ⟨hx, fun φ => by rw [he]; exact (hn φ).2⟩
  obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h0 : (0 : V) ∉ (finite_boxSet hK hF T).toFinset.biUnion Fn := by
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn, Set.mem_setOf_eq, not_exists, not_and]
    intro n hn _ he
    have h1 := (hn φ0).1
    rw [← he] at h1
    simp at h1
  have hdisj : ∀ n ∈ (finite_boxSet hK hF T).toFinset, ∀ m ∈ (finite_boxSet hK hF T).toFinset,
      n ≠ m → Disjoint (Fn n) (Fn m) := by
    intro n _ m _ hnm
    rw [Finset.disjoint_left]
    intro x hxn hxm
    simp only [Fn, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hxn hxm
    apply hnm
    exact RingOfIntegers.ext ((algebraMap F K).injective (hxn.2.symm.trans hxm.2))
  unfold ballCount
  rw [← Set.coe_setOf, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem h0, Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold repCount
  rw [← Set.coe_setOf, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (StabilizerLattices.finite_rep hd hM _)]
end Formalism.HermitianLattices.Ext.L3.BallSum
