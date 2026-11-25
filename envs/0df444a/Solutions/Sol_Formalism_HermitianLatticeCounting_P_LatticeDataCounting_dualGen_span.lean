-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.dualGen_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:58.476621+00:00
-- url     : https://prove2.me/submissions/c11ebc71-9cc0-4eec-8428-58d2eee77e6c

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_latGen
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_fg_of_smul_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_star_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_mem_sup_span_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.LatticeDataCounting
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U]
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution (h : U →ₗ[E] U →ₗ⋆[E] E) (M N : Submodule (𝓞 E) U) (e : ℕ) (s : Fin e → U)
    (hfin : N.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0)
    (hM : M ≤ N ⊔ Submodule.span (𝓞 E) (Set.range s)) (hs : ∀ i, s i ∈ M) :
    ∃ t : Fin e → U, (∀ i, t i ∈ hdualSub h N) ∧
      hdualSub h N ≤ hdualSub h M ⊔ Submodule.span (𝓞 E) (Set.range t) := by
  let φ : U →ₗ[𝓞 E] (Fin e → E) :=
    LinearMap.pi fun i => (h.flip (s i)).restrictScalars (𝓞 E)
  have hφ : ∀ x i, φ x i = h x (s i) := fun x i => rfl
  let A : Submodule (𝓞 E) (Fin e → E) := LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin e))
  have hA : ∀ v : Fin e → E, v ∈ A ↔ ∀ i, v i ∈ (algebraMap (𝓞 E) E).range := by
    intro v
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, rfl⟩
    · intro hv
      choose c hc using hv
      exact ⟨c, funext hc⟩
  have hAfg : A.FG := by
    show (LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin e))).FG
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  let B : Submodule (𝓞 E) (Fin e → E) := (hdualSub h N).map φ
  set n := N.toAddSubgroup.relIndex M.toAddSubgroup with hn
  have hd : ((n : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hfin
  have hdB : ∀ v ∈ B, ((n : ℕ) : 𝓞 E) • v ∈ A := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hA]
    intro i
    have h1 : n • s i ∈ N.toAddSubgroup := AddSubgroup.nsmul_relIndex_mem _ (hs i)
    have h2 := hx (n • s i) h1
    rw [map_nsmul] at h2
    rw [Nat.cast_smul_eq_nsmul, Pi.smul_apply, hφ]
    exact h2
  have hBfg : B.FG := fg_of_smul_le A B hAfg _ hd hdB
  obtain ⟨t', ht', hBt⟩ := latGen e (by simp) A B hBfg _ hd hdB
  choose t ht using ht'
  refine ⟨t, fun i => (ht i).1, ?_⟩
  intro x hx
  have h1 : φ x ∈ A ⊔ Submodule.span (𝓞 E) (Set.range t') := hBt ⟨x, hx, rfl⟩
  obtain ⟨c, hc⟩ := (mem_sup_span_iff A t' (φ x)).mp h1
  rw [mem_sup_span_iff]
  refine ⟨c, ?_⟩
  set x' := x - ∑ i, c i • t i with hx'
  have hx'N : x' ∈ hdualSub h N :=
    Submodule.sub_mem _ hx (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ht i).1)
  have hφx' : φ x' ∈ A := by
    have : φ x' = φ x - ∑ i, c i • t' i := by
      rw [hx', map_sub, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, (ht i).2]
    rw [this]; exact hc
  rw [hA] at hφx'
  intro m hm
  obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp (hM hm)
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hy
  rw [map_add, map_sum]
  refine (algebraMap (𝓞 E) E).range.add_mem (hx'N a ha) (Subring.sum_mem _ fun i _ => ?_)
  rw [← algebraMap_smul E (b i) (s i), LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
  exact (algebraMap (𝓞 E) E).range.mul_mem (star_mem (b i)) (hφx' i)
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
