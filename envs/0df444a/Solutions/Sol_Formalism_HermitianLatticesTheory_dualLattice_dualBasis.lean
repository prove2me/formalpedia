-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.dualLattice_dualBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:01.530475+00:00
-- url     : https://prove2.me/submissions/c738f995-dfe6-4715-8458-71772ad7a9d6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : h.Nondegenerate) (b : Basis ι K V) :
    ∃ bs : ι → V, ∀ i j, h (b i) (bs j) = if i = j then 1 else 0 := by
  classical
  haveI := Module.Finite.of_basis b
  let T : V →ₗ[K] (ι → K) := LinearMap.pi fun i => h (b i)
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ i, h (b i) x = 0 := fun i => congrFun hx i
    have hflip : h.flip x = 0 := b.ext fun i => by simp [h0 i]
    exact hnd.2 x fun y => by simpa using LinearMap.congr_fun hflip y
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Module.finrank_eq_card_basis b])).mp hinj
  choose bs hbs using fun j => hsurj (Pi.single j 1)
  refine ⟨bs, fun i j => ?_⟩
  have := congrFun (hbs j) i
  simpa [T, Pi.single_apply] using this
end Formalism.HermitianLatticesTheory
