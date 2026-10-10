-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepDirect.WFam_isInternal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:59:05.393159+00:00
-- url     : https://prove2.me/submissions/c8bb8591-6b31-4572-90e9-310fc46f2a46

-- Generated from ChapterLorentzRealRepDirect.lean — solution of BookProof.ChapterLorentzRealRepDirect.WFam_isInternal
import Mathlib
import Definitions.Def_ChapterLorentzRealRepDirect
import Theorems.Thm_BookProof_ChapterLorentzRealRepDirect_iSup_WFam_eq_top
import Theorems.Thm_BookProof_ChapterLorentzRealRepDirect_sum_finrank_WFam
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRepFull
open BookProof.ChapterLorentzRealRepDirect



open Matrix Module


open BookProof.ChapterLorentzRealRep BookProof.ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepFull

set_option maxHeartbeats 1000000 in
theorem solution : DirectSum.IsInternal WFam := by

  refine ⟨ ?_, ?_ ⟩;
  · intro x y hxy;
    have h_inj : Function.Injective (DirectSum.coeLinearMap WFam) := by
      have h_surj : LinearMap.range (DirectSum.coeLinearMap WFam) = ⊤ := by
        rw [ DirectSum.range_coeLinearMap ];
        convert iSup_WFam_eq_top using 1;
      have h_finrank : Module.finrank ℝ (DirectSum (Fin 4) fun i => WFam i) = Module.finrank ℝ
          (Matrix (Fin 4) (Fin 4) ℝ) := by
        convert sum_finrank_WFam using 1;
        convert Module.finrank_directSum ℝ ( fun i => WFam i );
      exact ( OrzechProperty.bijective_of_surjective_of_finrank_le
          ( DirectSum.coeLinearMap WFam ) ( LinearMap.range_eq_top.mp h_surj )
          ( le_of_eq h_finrank ) ).injective;
    exact h_inj hxy;
  · convert LinearMap.range_eq_top.mp ( show LinearMap.range ( DirectSum.coeLinearMap WFam ) = ⊤
      from ?_ ) using 1
    · rfl
    · rw [ DirectSum.range_coeLinearMap ]
      exact iSup_WFam_eq_top
