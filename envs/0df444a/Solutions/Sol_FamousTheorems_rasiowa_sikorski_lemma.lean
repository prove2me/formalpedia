-- Prove2me | solution 1 for FamousTheorems.rasiowa_sikorski_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:13:46.940704+00:00
-- url     : https://prove2.me/submissions/b3ac23e8-6311-496b-aee3-68d2abd42b57

import Mathlib

theorem solution {P : Type*} [Preorder P] (p : P) {ι : Type*} [Encodable ι] (𝒟 : ι → Order.Cofinal P) :
    ∃ I : Order.Ideal P, p ∈ I ∧ ∀ i, ∃ x ∈ 𝒟 i, x ∈ I :=
  ⟨Order.idealOfCofinals p 𝒟, Order.mem_idealOfCofinals p 𝒟, Order.cofinal_meets_idealOfCofinals p 𝒟⟩
