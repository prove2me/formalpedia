-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.mackey_product
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:17.494865+00:00
-- url     : https://prove2.me/submissions/b4cd465e-55c1-43a4-b8e9-a67cb116738a

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : MackeyProd := by
  unfold MackeyProd
  intro ι A _ _ _ P _ U ψ hψ
  unfold IsMackey
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_eq_one fun v _ => (hψ v).1
  · intro u hu u' hu'
    dsimp only
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hu1 : ∀ v ∈ (Set.univ : Set ι), u v ∈ U v := hu
    have hu2 : ∀ v ∈ (Set.univ : Set ι), u' v ∈ U v := hu'
    exact (hψ v).2.1 _ (hu1 v (Set.mem_univ v)) _ (hu2 v (Set.mem_univ v))
  · intro h hh
    have hex : ∃ v0, h v0 ∉ U v0 := by
      by_contra hc
      push_neg at hc
      apply hh
      show ∀ v ∈ (Set.univ : Set ι), h v ∈ U v
      exact fun v _ => hc v
    obtain ⟨v0, hv0⟩ := hex
    obtain ⟨u0, hu0, hc, hne⟩ := (hψ v0).2.2 (h v0) hv0
    refine ⟨Pi.mulSingle v0 u0, ?_, ?_, ?_⟩
    · show ∀ v ∈ (Set.univ : Set ι), Pi.mulSingle v0 u0 v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hu0
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∀ v ∈ (Set.univ : Set ι), (h⁻¹ * Pi.mulSingle v0 u0 * h) v ∈ U v
      intro v _
      by_cases hv : v = v0
      · subst hv
        simpa using hc
      · simp [Pi.mulSingle_eq_of_ne hv]
    · show ∏ v, ψ v ((h⁻¹ * Pi.mulSingle v0 u0 * h) v) ≠ ∏ v, ψ v (Pi.mulSingle v0 u0 v)
      rw [Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1]),
        Fintype.prod_eq_single v0 (fun v hv => by simp [Pi.mulSingle_eq_of_ne hv, (hψ v).1])]
      simpa using hne
end Formalism.EigenvalueLevelCeiling
