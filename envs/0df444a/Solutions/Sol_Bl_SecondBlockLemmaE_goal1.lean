-- Prove2me | solution 1 for Bl.SecondBlockLemmaE.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:40.844563+00:00
-- url     : https://prove2.me/submissions/39e24664-dfc5-40cc-9817-1d71378dc8c1

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasD_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open Bl Bl.SecondBlockLemmaE
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace Bl.SecondBlockLemmaE
theorem _root_.solution {Λ : Submodule (𝓞 E) V} {v : V}
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e1 : (d₁ * d₂) • x = d₂ • (d₁ • x) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • y = d₁ • (d₂ • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Λ.add_mem (Λ.smul_mem _ h₁) (Λ.smul_mem _ h₂)
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) a
    refine ⟨(m : 𝓞 E) * d, mul_ne_zero (nonZeroDivisors.ne_zero m.2) hd, ?_⟩
    have key : (m : 𝓞 E) • (a • x) = n • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm]
      rw [hnm, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_comm d n x]
    exact Λ.smul_mem _ h
end Bl.SecondBlockLemmaE
