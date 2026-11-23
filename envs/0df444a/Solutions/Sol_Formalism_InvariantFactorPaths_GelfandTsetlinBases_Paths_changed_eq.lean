-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.changed_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:49.438794+00:00
-- url     : https://prove2.me/submissions/7cd7c186-5165-4a52-80f9-d674478179fc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_le_iff_lt_colHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_le
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_strip_height

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) :
    {c : ℤ | colHeight ν c ≠ colHeight μ c} =
      ↑(univ.biUnion fun m : Fin n => Finset.Ioc (μ m) (ν m)) := by
  ext c
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_Ioc]
  constructor
  · intro hne
    have hh := strip_height hν hμ hs c
    have hn := colHeight_le ν c
    refine ⟨⟨colHeight μ c, by omega⟩, ?_, ?_⟩
    · refine not_le.1 fun hle => ?_
      exact absurd ((le_iff_lt_colHeight hμ c _).1 hle) (lt_irrefl _)
    · refine (le_iff_lt_colHeight hν c _).2 ?_
      show colHeight μ c < colHeight ν c
      omega
  · rintro ⟨m, m1, m2⟩
    have a1 := (le_iff_lt_colHeight hν c m).1 m2
    have a2 : ¬ m.val < colHeight μ c := fun hlt =>
      absurd ((le_iff_lt_colHeight hμ c m).2 hlt) (not_le.2 m1)
    omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
