-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.mem_lowW_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:18.311281+00:00
-- url     : https://prove2.me/submissions/36053873-09ee-4fc6-ac72-3baefad42b35

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ)
    (wi : Matrix (Fin s.sum) (Fin s.sum) K) (h1 : wi * pt s t = 1) (h2 : pt s t * wi = 1)
    (g : GL (Fin s.sum) K) :
    g ∈ lowW K s t ↔ IsLowUni (g : Matrix (Fin s.sum) (Fin s.sum) K) ∧
      IsLowUni (wi * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) := by
  show (IsLowUni (g : Matrix (Fin s.sum) (Fin s.sum) K) ∧ ∃ h : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni h ∧
    (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t = pt s t * h) ↔ _
  constructor
  · rintro ⟨hg, h, hh, he⟩
    refine ⟨hg, ?_⟩
    have hw : wi * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t = h := by
      rw [Matrix.mul_assoc, he, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [hw]; exact hh
  · rintro ⟨hg, hh⟩
    refine ⟨hg, _, hh, ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
end Formalism.DoubleCosetMeasures.P.Supp
