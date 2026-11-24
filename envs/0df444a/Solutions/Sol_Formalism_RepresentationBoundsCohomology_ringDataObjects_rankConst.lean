-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.rankConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:20.655114+00:00
-- url     : https://prove2.me/submissions/4ce2657e-1a89-40ca-9cf9-edb38c10788b

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_CharpolyRevMap
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_idem_normal_form
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_rank_map_conj
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_charpolyRev_conj
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_resConst


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
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
open Polynomial
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution : StatRankConst := by
  unfold StatRankConst
  intro O _ _ _ X T d _ _ hT e he hcoef x y
  classical
  have hid : ∀ z, IsIdempotentElem (e z) := fun z => congrFun he z
  choose P Q dd hdd hPQ hQP heq using fun z => idem_normal_form (e z) (hid z)
  have hrk : ∀ z, ((e z).map (algebraMap O (FractionRing O))).rank = Nat.card {j // dd z j = 1} := by
    intro z
    rw [heq z]
    exact rank_map_conj _ (P z) (Q z) (dd z) (hdd z) (hPQ z) (hQP z)
  have hcp : ∀ z, (e z).charpolyRev = (1 - Polynomial.X) ^ Nat.card {j // dd z j = 1} := by
    intro z
    rw [heq z]
    exact charpolyRev_conj (P z) (Q z) (dd z) (hdd z) (hPQ z)
  rw [hrk, hrk]
  have hres : ∀ k, IsLocalRing.residue O
      (((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd x j = 1}).coeff k) =
      IsLocalRing.residue O (((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd y j = 1}).coeff k) := by
    intro k
    have := resConst O X T hT _ (hcoef k) x y
    simpa only [hcp] using this
  have hpoly : ((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd x j = 1}).map (IsLocalRing.residue O) =
      ((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd y j = 1}).map (IsLocalRing.residue O) := by
    ext k
    simp only [Polynomial.coeff_map]
    exact hres k
  have hdeg : ∀ m : ℕ, (((1 - Polynomial.X : Polynomial O) ^ m).map (IsLocalRing.residue O)).natDegree = m := by
    intro m
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.natDegree_pow,
      Polynomial.natDegree_sub_eq_right_of_natDegree_lt] <;> simp
  have := congrArg Polynomial.natDegree hpoly
  rwa [hdeg, hdeg] at this
end Formalism.RepresentationBoundsCohomology.ringDataObjects
