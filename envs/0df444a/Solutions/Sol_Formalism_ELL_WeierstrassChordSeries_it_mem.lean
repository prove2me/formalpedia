-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.it_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:35.599577+00:00
-- url     : https://prove2.me/submissions/cd2ea0a6-9dc9-420f-8261-a28aada16c9e

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
variable {W}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (S : Subalgebra ℤ K) (hS : ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) ⊆ S) :
    ∀ k, it W k ∈ (PowerSeries.map (algebraMap S K)).range := by
  have hX : (X : PowerSeries K) ∈ (PowerSeries.map (algebraMap S K)).range :=
    RingHom.mem_range.mpr ⟨X, PowerSeries.map_X _⟩
  have hC : ∀ a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K),
      (C a : PowerSeries K) ∈ (PowerSeries.map (algebraMap S K)).range := fun a ha =>
    RingHom.mem_range.mpr ⟨C ⟨a, hS ha⟩, by rw [PowerSeries.map_C]; rfl⟩
  have h1 := hC W.a₁ (by simp)
  have h2 := hC W.a₂ (by simp)
  have h3 := hC W.a₃ (by simp)
  have h4 := hC W.a₄ (by simp)
  have h6 := hC W.a₆ (by simp)
  intro k
  induction k with
  | zero => exact zero_mem _
  | succ k ih =>
    show fw W (it W k) ∈ _
    unfold fw
    exact add_mem (add_mem (add_mem (add_mem (add_mem (pow_mem hX 3) (mul_mem (mul_mem h1 hX) ih))
      (mul_mem (mul_mem h2 (pow_mem hX 2)) ih)) (mul_mem h3 (pow_mem ih 2)))
      (mul_mem (mul_mem h4 hX) (pow_mem ih 2))) (mul_mem h6 (pow_mem ih 3))
end Formalism.ELL.WeierstrassChordSeries
