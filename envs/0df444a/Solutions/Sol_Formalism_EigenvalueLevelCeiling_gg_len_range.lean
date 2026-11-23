-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.gg_len_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:04.28871+00:00
-- url     : https://prove2.me/submissions/54fb72ad-7f35-4300-a916-a765c2fbc2ee

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG

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
variable {R : Type*} [CommRing R] {Y Q : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup Q]
  [Module R Q]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (n : R) (s : ι → Y →ₗ[R] Q)
    (t : ι → Q →ₗ[R] Y) (hts : ∀ i j y, t i (s j y) = if i = j then n • y else 0) :
    (Fintype.card ι : ℕ∞) * Module.length R (LinearMap.range (n • (LinearMap.id : Y →ₗ[R] Y))) ≤
      Module.length R Q := by
  set NY := LinearMap.range (n • (LinearMap.id : Y →ₗ[R] Y)) with hNY
  have h1 : Module.length R (ι → NY) = (Fintype.card ι : ℕ∞) * Module.length R NY := by
    rw [Module.length_pi_of_fintype]
    simp
  rw [← h1]
  let T : Q →ₗ[R] (ι → Y) := LinearMap.pi t
  have h2 : Module.length R (LinearMap.range T) ≤ Module.length R Q :=
    Module.length_le_of_surjective T.rangeRestrict T.surjective_rangeRestrict
  refine le_trans ?_ h2
  let incl : (ι → NY) →ₗ[R] (ι → Y) := LinearMap.pi (fun i => NY.subtype ∘ₗ LinearMap.proj i)
  have hin : ∀ f, incl f ∈ LinearMap.range T := by
    intro f
    have hf : ∀ i, ∃ y : Y, n • y = (f i : Y) := by
      intro i
      obtain ⟨y, hy⟩ := (f i).2
      exact ⟨y, by simpa using hy⟩
    choose y hy using hf
    refine ⟨∑ j, s j (y j), ?_⟩
    ext i
    simp [T, incl, hts, hy]
  refine Module.length_le_of_injective (incl.codRestrict _ hin) ?_
  intro f g hfg
  have h3 : incl f = incl g := congrArg Subtype.val hfg
  ext i
  exact congrFun h3 i
end Formalism.EigenvalueLevelCeiling
