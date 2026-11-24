-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.LatticeLiftIndependence.reps_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:23.221833+00:00
-- url     : https://prove2.me/submissions/e289c61c-a50e-474e-ab2a-e7d2632fe1f4

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.LatticeLiftIndependence
open Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.ThetaLiftIndependence.LatticeLiftIndependence
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    {s : Finset (Submodule (NumberField.RingOfIntegers K) V)} (hs : IsClassReps h L s)
    {N N' N'' : Submodule (NumberField.RingOfIntegers K) V} (hN : N ∈ s) (hN'' : N'' ∈ s)
    {g g' : V ≃ₗ[K] V} (hg : g ∈ isom h) (hg' : g' ∈ isom h)
    (e : gmap g N' = N) (e' : gmap g' N'' = N') : N'' = N := by
  obtain ⟨N0, -, huniq⟩ := hs.2 N (hs.1 N hN)
  have h1 := huniq N ⟨hN, 1, (isom h).one_mem, gmap_one N⟩
  have h2 := huniq N'' ⟨hN'', g * g', (isom h).mul_mem hg hg', by rw [gmap_mul, e', e]⟩
  exact h2.trans h1.symm
end Formalism.ThetaLiftIndependence.LatticeLiftIndependence
