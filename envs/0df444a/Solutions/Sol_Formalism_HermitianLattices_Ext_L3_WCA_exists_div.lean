-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCA.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:11.590735+00:00
-- url     : https://prove2.me/submissions/ab750cde-7d21-415c-ac3f-da1af419f5f9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.WCA
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1)) :
    ∃ s : 𝓞 F, s ∉ 𝔭 ∧ ∀ k : ℕ, ∀ z ∈ extP K 𝔭 ^ (v + k), ∃ z' ∈ extP K 𝔭 ^ k, ι s * z = ι n * z' := by
  have hc' : Ideal.span {n} ≠ (0 : Ideal (𝓞 F)) := by simpa using hn
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact h𝔭.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨s, hsb, hsp⟩ := SetLike.not_le_iff_exists.mp hnd
  set m := multiplicity 𝔭 (Ideal.span {n}) with hm
  have hmv : m ≤ v := by
    by_contra hlt
    rw [not_le] at hlt
    apply hv
    have h1 : Ideal.span {n} ≤ 𝔭 ^ m := hb.le.trans Ideal.mul_le_left
    exact Ideal.pow_le_pow_right hlt (h1 (Ideal.mem_span_singleton_self n))
  refine ⟨s, hsp, fun k z hz => ?_⟩
  have h2 : Ideal.span {s} * 𝔭 ^ (v + k) ≤ Ideal.span {n} * 𝔭 ^ k := by
    rw [pow_add, ← mul_assoc]
    refine Ideal.mul_mono_left ?_
    rw [hb, mul_comm]
    exact Ideal.mul_mono (Ideal.pow_le_pow_right hmv) ((Ideal.span_singleton_le_iff_mem _).2 hsb)
  have h3 := Ideal.map_mono (f := ι) h2
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_pow, Ideal.map_pow, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton] at h3
  have h4 : ι s * z ∈ Ideal.span {ι n} * extP K 𝔭 ^ k :=
    h3 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)
  obtain ⟨z', hz', e⟩ := Ideal.mem_span_singleton_mul.1 h4
  exact ⟨z', hz', e.symm⟩
end Formalism.HermitianLattices.Ext.L3.WCA
