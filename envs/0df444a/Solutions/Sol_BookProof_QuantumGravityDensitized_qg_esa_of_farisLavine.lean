-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.qg_esa_of_farisLavine
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:50:09.651689+00:00
-- url     : https://prove2.me/submissions/f348182a-4184-4e36-a8ad-460effaac71c

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.qg_esa_of_farisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_of_farisLavine
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N) (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := essentiallySelfAdjointOn_of_farisLavine H N c hH hN hc hNpos hNsurj hcomm
