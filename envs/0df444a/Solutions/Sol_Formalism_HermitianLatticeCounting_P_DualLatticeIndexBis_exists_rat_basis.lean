-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_rat_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:13.109954+00:00
-- url     : https://prove2.me/submissions/1eaf0e45-6be9-4717-b765-728f386d6212

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

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
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution {V ι : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V] (L : Submodule ℤ V)
    (c : Module.Basis ι ℤ L) (hL : ∀ x : V, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L) :
    ∃ cb : Module.Basis ι ℚ V, (∀ i, cb i = (c i : V)) ∧ L = Submodule.span ℤ (Set.range cb) := by
  have hLv : L = Submodule.span ℤ (Set.range (fun i => (c i : V))) := by
    have : Set.range (fun i => (c i : V)) = L.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent ℚ (fun i => (c i : V)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (c.linearIndependent.map' L.subtype (Submodule.ker_subtype L))
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range (fun i => (c i : V))) := by
    intro x _
    obtain ⟨n, hn, hnx⟩ := hL x
    rw [hLv] at hnx
    have h1 : n • x ∈ Submodule.span ℚ (Set.range (fun i => (c i : V))) :=
      Submodule.span_subset_span ℤ ℚ _ hnx
    have h2 : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ n x, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  refine ⟨Module.Basis.mk hli hsp, fun i => by simp, ?_⟩
  rw [Module.Basis.coe_mk]
  exact hLv
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
