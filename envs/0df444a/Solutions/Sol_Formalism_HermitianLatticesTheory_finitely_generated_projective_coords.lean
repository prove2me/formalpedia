-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.finitely_generated_projective_coords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:02.452899+00:00
-- url     : https://prove2.me/submissions/f5b338cc-68ec-41b3-ba47-e25883d5ecbc

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
omit [IsFractionRing R K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (L : Submodule R V) (hL : L.FG) (hK : Function.Injective (algebraMap R K)) :
    ∃ (n : ℕ) (g : Fin n → L) (f : Fin n → (L →ₗ[R] R)), ∀ y : L, y = ∑ i, f i y • g i := by
  classical
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have htor : Submodule.torsion R L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have ha' : (algebraMap R K (a : R)) • (x : V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val ha
    have hne : algebraMap R K (a : R) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R K)]
      exact fun h0 => nonZeroDivisors.ne_zero a.2 (hK h0)
    exact Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)
  haveI : Module.Flat R L := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R L
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i => π (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ σ, fun y => ?_⟩
  have e1 : π (σ y) = y := LinearMap.congr_fun hσ y
  have e2 : σ y = ∑ i, σ y i • (Pi.single i (1 : R) : Fin n → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← e1, e2]
  simp [map_sum, map_smul]
end Formalism.HermitianLatticesTheory
