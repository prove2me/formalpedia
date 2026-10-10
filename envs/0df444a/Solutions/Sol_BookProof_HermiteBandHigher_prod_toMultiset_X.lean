-- Prove2me | solution 1 for BookProof.HermiteBandHigher.prod_toMultiset_X
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:58:55.46599+00:00
-- url     : https://prove2.me/submissions/f8dd76c2-0371-41b4-b67b-d22b937f6434

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.prod_toMultiset_X
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin d →₀ ℕ) :
    ((s.toMultiset.map (fun i => (X i : MvPolynomial (Fin d) ℂ))).prod)
      = s.prod fun i k => (X i : MvPolynomial (Fin d) ℂ) ^ k := by

  classical
  induction s using Finsupp.induction with
  | zero => simp
  | single_add a b f _ha _hb ih =>
      rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.map_add, Multiset.prod_add,
        ih, Finsupp.prod_add_index' (fun i => pow_zero (X i : MvPolynomial (Fin d) ℂ))
          (fun i k₁ k₂ => pow_add (X i : MvPolynomial (Fin d) ℂ) k₁ k₂)]
      have hR : ((Finsupp.single a b).prod fun i k => (X i : MvPolynomial (Fin d) ℂ) ^ k)
          = (X a : MvPolynomial (Fin d) ℂ) ^ b :=
        Finsupp.prod_single_index (pow_zero _)
      have hL : (Multiset.map (fun i => (X i : MvPolynomial (Fin d) ℂ))
            (b • ({a} : Multiset (Fin d)))).prod = (X a : MvPolynomial (Fin d) ℂ) ^ b := by
        rw [Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul,
          Multiset.prod_singleton]
      rw [hL, hR]
