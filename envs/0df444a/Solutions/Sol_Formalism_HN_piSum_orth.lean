-- Prove2me | solution 1 for Formalism.HN.piSum_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:27.435807+00:00
-- url     : https://prove2.me/submissions/adc5b622-149c-429e-a469-a893738eceb6

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_T_vanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (ρ : ∀ i, V i →+ E i)
private theorem piReal_apply (ρ : ∀ i, V i →+ E i) (x : ∀ i, V i) (j : ι) :
    piReal ρ x j = ρ j (x j) := by
  rfl
variable [∀ i, FiniteDimensional ℝ (E i)]
end
section
variable {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
end
section
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
end
end Formalism.HN
namespace Formalism.HN
universe uR uι uV uE uS
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
namespace Formalism.HN
theorem _root_.solution (ρ : ∀ i, V i →+ E i) (L : ∀ i, Submodule R (V i)) (a : ι) (s : Finset ι)
    (ha : a ∉ s) : ∀ x ∈ piSumS L a, ∀ y ∈ piSumT L s,
      inner ℝ (piReal ρ x) (piReal ρ y) = 0 := by
  intro x hx y hy
  obtain ⟨v, -, rfl⟩ := Submodule.mem_map.1 hx
  have hya : y a = 0 := piSum_T_vanish L s hy a ha
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [piReal_apply, piReal_apply]
  by_cases h : j = a
  · subst h
    rw [hya, map_zero, inner_zero_right]
  · rw [LinearMap.single_apply, Pi.single_eq_of_ne h, map_zero, inner_zero_left]
end Formalism.HN
