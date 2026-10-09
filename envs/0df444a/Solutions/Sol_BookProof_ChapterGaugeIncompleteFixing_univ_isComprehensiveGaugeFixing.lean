-- Prove2me | solution 1 for BookProof.ChapterGaugeIncompleteFixing.univ_isComprehensiveGaugeFixing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:30:00.023201+00:00
-- url     : https://prove2.me/submissions/3db6b37d-689f-4237-a98c-68e758ed1a91

-- Generated from ChapterGaugeIncompleteFixing.lean — solution of BookProof.ChapterGaugeIncompleteFixing.univ_isComprehensiveGaugeFixing
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing



open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution :
    IsComprehensiveGaugeFixing G (Set.univ : Set X) := fun x => ⟨x, Set.mem_univ x, 1, one_smul G x⟩
