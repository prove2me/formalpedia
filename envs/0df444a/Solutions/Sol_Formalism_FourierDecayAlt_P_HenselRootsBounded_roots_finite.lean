-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.roots_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:54.794822+00:00
-- url     : https://prove2.me/submissions/0d8ca011-3a2f-405b-8102-f37080f3a8fa

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution {K : Type} [CommRing K] [IsArtinianRing K] [IsReduced K] (s : ℕ) (hs : 1 ≤ s)
    (D : Kˣ) : {z : Kˣ | z ^ s = D}.Finite := by
  classical
  have h1 : {x : K | x ^ s = (D : K)}.Finite := by
    let e := IsArtinianRing.equivPi K
    have h2 : (Set.pi Set.univ fun I : MaximalSpectrum K =>
        {y : K ⧸ I.asIdeal | y ^ s = e (D : K) I}).Finite := by
      refine Set.Finite.pi fun I => ?_
      refine Set.Finite.subset (Polynomial.nthRoots s (e (D : K) I)).toFinset.finite_toSet ?_
      intro y hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots (by omega)).2 hy
    refine Set.Finite.subset (h2.preimage e.injective.injOn) ?_
    intro x hx
    rw [Set.mem_preimage, Set.mem_pi]
    intro I _
    show (e x I) ^ s = e (D : K) I
    have hx' : x ^ s = (D : K) := hx
    rw [← hx', map_pow]; rfl
  refine Set.Finite.subset (h1.preimage Units.val_injective.injOn) ?_
  intro z hz
  have hz' : z ^ s = D := hz
  show (z : K) ^ s = (D : K)
  rw [← hz']; simp
end Formalism.FourierDecayAlt.P.HenselRootsBounded
