-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.latGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:47.787379+00:00
-- url     : https://prove2.me/submissions/288d51c6-1ca5-4e57-aef6-6fc67e249984

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_quotGen_proof__1cc5bb5ca961
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_pad
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_LatticeDataCounting_finrank_sub_le

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
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
namespace Formalism.HermitianLatticeCounting.P.LatticeDataCounting
theorem _root_.solution [FiniteDimensional E V] (j : ℕ) (hj : Module.finrank E V ≤ j) (A B : Submodule (𝓞 E) V)
    (hB : B.FG) (d : 𝓞 E) (hd : d ≠ 0) (hdB : ∀ x ∈ B, d • x ∈ A) :
    ∃ t : Fin j → V, (∀ i, t i ∈ B) ∧ B ≤ A ⊔ Submodule.span (𝓞 E) (Set.range t) := by
  have : Module.Finite (𝓞 E) B := Module.Finite.iff_fg.mpr hB
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans E
  have : Module.IsTorsionFree (𝓞 E) B :=
    Function.Injective.moduleIsTorsionFree B.subtype B.injective_subtype (fun _ _ => rfl)
  have : Module.FinitePresentation (𝓞 E) B := Module.finitePresentation_of_finite (𝓞 E) B
  have : Module.Projective (𝓞 E) B := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := quotGen_proof' E B (Ideal.span {d}) (by simpa using hd)
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  obtain ⟨t, ht, hst⟩ := pad (R := 𝓞 E) ((finrank_sub_le B).trans hj) (fun i => (s' i : V)) B
    (fun i => (s' i).2)
  refine ⟨t, ht, ?_⟩
  have htop : Ideal.span {d} • (⊤ : Submodule (𝓞 E) B) ⊔ Submodule.span (𝓞 E) (Set.range s') = ⊤ := by
    rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
    have : ((Ideal.span {d} • (⊤ : Submodule (𝓞 E) B)).mkQ ∘ s') = s := funext hs'
    rw [this, hs]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈
      Ideal.span {d} • (⊤ : Submodule (𝓞 E) B) ⊔ Submodule.span (𝓞 E) (Set.range s') := by
    rw [htop]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx'
  have hyA : (y : V) ∈ A := by
    rw [Submodule.ideal_span_singleton_smul] at hy
    obtain ⟨y', _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    exact hdB _ y'.2
  have hzS : (z : V) ∈ Submodule.span (𝓞 E) (Set.range t) := by
    apply hst
    have h1 : B.subtype z ∈ (Submodule.span (𝓞 E) (Set.range s')).map B.subtype :=
      Submodule.mem_map_of_mem hz
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1
  have hxe : x = (y : V) + (z : V) := by
    have := congrArg Subtype.val hyz
    exact this.symm
  rw [hxe]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hyA) (Submodule.mem_sup_right hzS)
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
