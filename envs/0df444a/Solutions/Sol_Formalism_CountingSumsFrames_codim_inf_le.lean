-- Prove2me | solution 1 for Formalism.CountingSumsFrames.codim_inf_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:33.813048+00:00
-- url     : https://prove2.me/submissions/ff1070b0-78e1-4648-b234-549438bd33f2

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.CountingSumsFrames
theorem _root_.solution [DecidableEq ι] (Y : Submodule K V) [FiniteDimensional K Y] (A : ι → Submodule K V) :
    ∀ s : Finset ι, Module.finrank K Y - Module.finrank K (Y ⊓ s.inf A : Submodule K V) ≤
      ∑ i ∈ s, (Module.finrank K Y - Module.finrank K (Y ⊓ A i : Submodule K V)) := by
  have hle : ∀ {S T : Submodule K V} [FiniteDimensional K T], S ≤ T →
      Module.finrank K S ≤ Module.finrank K T :=
    fun h => LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective h)
  intro s
  induction s using Finset.induction_on with
  | empty => rw [Finset.inf_empty, inf_top_eq]; simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.inf_insert]
    have e : (Y ⊓ (A a ⊓ s.inf A) : Submodule K V) = (Y ⊓ A a) ⊓ (Y ⊓ s.inf A) := by
      rw [inf_inf_distrib_left]
    rw [e]
    haveI : FiniteDimensional K ↥(Y ⊓ A a) := Submodule.finiteDimensional_of_le inf_le_left
    haveI : FiniteDimensional K ↥(Y ⊓ s.inf A) := Submodule.finiteDimensional_of_le inf_le_left
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Y ⊓ A a) (Y ⊓ s.inf A)
    have h2 : Module.finrank K ↥((Y ⊓ A a) ⊔ (Y ⊓ s.inf A)) ≤ Module.finrank K Y :=
      hle (sup_le inf_le_left inf_le_left)
    have h3 : Module.finrank K ↥(Y ⊓ A a) ≤ Module.finrank K Y := hle inf_le_left
    have h4 : Module.finrank K ↥(Y ⊓ s.inf A) ≤ Module.finrank K Y := hle inf_le_left
    omega
end Formalism.CountingSumsFrames
