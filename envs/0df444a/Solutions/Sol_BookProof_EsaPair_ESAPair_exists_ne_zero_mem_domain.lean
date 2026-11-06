-- Prove2me | solution 1 for BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:27:32.983148+00:00
-- url     : https://prove2.me/submissions/c3b774c6-04c8-4006-8dcd-caf2dd248c34

import Definitions.Def_ChapterEsaPairDGamma
import Theorems.Thm_BookProof_SecondQuantizationCore_exists_ne_zero_mem_dGammaCoreDomain

open BookProof.DirectSumEsa
open BookProof.TensorCore
open BookProof.EsaPair
open BookProof.SecondQuantizationCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem solution {a : Hs.carrier} (haD : a ∈ P.coreDomain)
    (ha0 : a ≠ 0) :
    ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n), f ≠ 0 := by
  exact BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain
    Hs P.closureDomain P.coreDomain P.sub_domain haD ha0
