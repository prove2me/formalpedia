-- Prove2me | solution 1 for BookProof.ChapterA.conjFixed_isSubsystem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:39.547207+00:00
-- url     : https://prove2.me/submissions/13693f59-67bf-407f-ab16-00e57295a737

-- Generated from ChapterA1f.lean — solution of BookProof.ChapterA.conjFixed_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1f
import Theorems.Thm_BookProof_ChapterA_conjFixed_isClosed
import Theorems.Thm_BookProof_ChapterA_conjFixed_invariant
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) :
    (rxSystem M).IsSubsystem (conjFixed θ) := ⟨conjFixed_isClosed θ, conjFixed_invariant M θ hθ⟩
