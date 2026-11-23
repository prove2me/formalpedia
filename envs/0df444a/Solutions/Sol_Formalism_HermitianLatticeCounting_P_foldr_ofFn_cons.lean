-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.foldr_ofFn_cons
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:07:32.88183+00:00
-- url     : https://prove2.me/submissions/69943fe5-9a87-44af-8bbe-d7e811ae87ec

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.foldr_ofFn_cons {W ι : Type} (Eop : ι → W → W) (q : ℕ) (i : ι) (τ : Fin q → ι) (w : W) :
    (List.ofFn (Fin.cons i τ : Fin (q + 1) → ι)).foldr Eop w = Eop i ((List.ofFn τ).foldr Eop w) := by
  simp [List.ofFn_succ]


theorem solution {W ι : Type} (Eop : ι → W → W) (q : ℕ) (i : ι) (τ : Fin q → ι) (w : W) :
    (List.ofFn (Fin.cons i τ : Fin (q + 1) → ι)).foldr Eop w = Eop i ((List.ofFn τ).foldr Eop w) :=
  Formalism.HermitianLatticeCounting.P.foldr_ofFn_cons Eop q i τ w
