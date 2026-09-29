-- Prove2me | solution 1 for FamousTheorems.iwasawa_simplicity_criterion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:59:59.159982+00:00
-- url     : https://prove2.me/submissions/446172dc-29e3-4473-a51f-5e94146286f3

import Mathlib

theorem solution {M : Type*} [Group M] {α : Type*} [MulAction M α] [Nontrivial M] (hc : commutator M = ⊤)
    [MulAction.IsQuasiPreprimitive M α] (IwaS : MulAction.IwasawaStructure M α) (hf : FaithfulSMul M α) :
    IsSimpleGroup M :=
  MulAction.IwasawaStructure.isSimpleGroup hc IwaS hf
