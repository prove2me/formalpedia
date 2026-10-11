-- Prove2me | solution 1 for BookProof.TempleSeparationNecessary.witness_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:46.316407+00:00
-- url     : https://prove2.me/submissions/83e1c54d-400f-4a5a-9fce-936180b9b394

-- Generated from ChapterTempleSeparationNecessary.lean — solution of BookProof.TempleSeparationNecessary.witness_apply
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Definitions.Def_ChapterRitzCertificate
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.TempleSeparationNecessary



noncomputable section


open BookProof.RitzCertificate

set_option maxHeartbeats 1000000 in
theorem solution (M : ℝ) (x y : E2) :
    witness M x y = ((-M : ℝ) : ℂ) • (y - (inner ℂ x y : ℂ) • x) := rfl
