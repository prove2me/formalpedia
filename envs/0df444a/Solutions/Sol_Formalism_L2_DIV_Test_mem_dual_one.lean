-- Prove2me | solution 1 for Formalism.L2.DIV.Test.mem_dual_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:49.632327+00:00
-- url     : https://prove2.me/submissions/2a85cf65-ab05-4233-9f58-708e27a17ecd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section Sub
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
end Sub
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
section Basic
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
end Roots
private theorem int_iff_lemma {K : Type} [Field K] [NumberField K] (x : K) :
    (∃ b : 𝓞 K, (b : K) = x) ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨b, rfl⟩
    first
    | exact NumberField.RingOfIntegers.isIntegral_coe b
    | exact b.2
    | exact (mem_integralClosure_iff ℤ K).mp b.2
  · intro h
    first
    | exact ⟨⟨x, h⟩, rfl⟩
    | exact ⟨⟨x, (mem_integralClosure_iff ℤ K).mpr h⟩, rfl⟩
section Chars
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Chars
section Conj
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Conj
section Assemble
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
end Assemble
section Schur
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
end Schur
end Formalism.L2.DIV
namespace Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
end Formalism.L2.DIV.Test
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution (y : K) :
    y ∈ Formalism.HermitianLatticesTheory.dual (stdPair K) (1 : Submodule (𝓞 K) K) ↔ y ∈ (1 : Submodule (𝓞 K) K) := by
  have key : y ∈ Formalism.HermitianLatticesTheory.dual (stdPair K) (1 : Submodule (𝓞 K) K) ↔
      ∀ z ∈ (1 : Submodule (𝓞 K) K), stdPair K z y ∈ (1 : Submodule (𝓞 K) K) := by
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  rw [key]
  constructor
  · intro h
    have h1 := h 1 (by rw [Submodule.mem_one]; exact ⟨1, map_one _⟩)
    rwa [stdPair_apply, star_one, one_mul] at h1
  · intro hy z hz
    rw [stdPair_apply]
    rw [Submodule.mem_one] at hy hz ⊢
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨b, rfl⟩ := hy
    have ha : IsIntegral ℤ (algebraMap (𝓞 K) K a) := (int_iff_lemma _).mp ⟨a, rfl⟩
    have hb : IsIntegral ℤ (algebraMap (𝓞 K) K b) := (int_iff_lemma _).mp ⟨b, rfl⟩
    have hs : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) := ha.map (starRingEnd K).toIntAlgHom
    obtain ⟨c, hc⟩ := (int_iff_lemma _).mpr (hs.mul hb)
    exact ⟨c, hc⟩
end Formalism.L2.DIV.Test
