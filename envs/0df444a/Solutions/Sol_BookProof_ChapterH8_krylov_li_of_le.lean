-- Prove2me | solution 1 for BookProof.ChapterH8.krylov_li_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:46:22.425987+00:00
-- url     : https://prove2.me/submissions/33ba1896-871c-4c4e-a042-919ff9db3f5e

import Mathlib
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8

set_option autoImplicit false

noncomputable section

open BookProof.ChapterH8 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6 ContinuousLinearMap in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {H : E →ₗ[ℂ] E} {v : E} {m n : ℕ} (hmn : m ≤ n)
    (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    LinearIndependent ℂ (fun i : Fin m => (H ^ (i : ℕ)) v) := by
  exact hli.comp (Fin.castLE hmn) (Fin.castLE_injective hmn)

end
