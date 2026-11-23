-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.LatticeDataCounting.mem_sup_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:45.218068+00:00
-- url     : https://prove2.me/submissions/5eda1629-2775-4192-84b9-bbdb4042a4ba

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting

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
theorem _root_.solution {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X] {n : ℕ} (N : Submodule R X)
    (t : Fin n → X) (x : X) :
    x ∈ N ⊔ Submodule.span R (Set.range t) ↔ ∃ c : Fin n → R, x - ∑ i, c i • t i ∈ N := by
  constructor
  · intro hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
    exact ⟨c, by simpa using ha⟩
  · rintro ⟨c, hc⟩
    have : x = (x - ∑ i, c i • t i) + ∑ i, c i • t i := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hc)
      (Submodule.mem_sup_right ((Submodule.mem_span_range_iff_exists_fun R).mpr ⟨c, rfl⟩))
end Formalism.HermitianLatticeCounting.P.LatticeDataCounting
