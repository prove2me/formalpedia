-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.radical_image_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:52.851335+00:00
-- url     : https://prove2.me/submissions/c815eecf-26dc-4cfb-a6fe-8b9459b2479e

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : RadImageIndex := by
  intro E _ _ cc α α' rr hcc hrr K H hH hK
  obtain ⟨d, hd, hden⟩ := cc.isFractional
  have hd0 : (d : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  let φ : 𝓞 E →ₗ[𝓞 E] E := LinearMap.toSpanSingleton (𝓞 E) E (d : E)⁻¹
  have hφ : ∀ a : 𝓞 E, φ a = (a : E) * (d : E)⁻¹ := fun a => by
    simp [φ, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  have hφinj : Function.Injective φ.toAddMonoidHom := by
    intro a b hab
    have : (a : E) * (d : E)⁻¹ = (b : E) * (d : E)⁻¹ := by rw [← hφ, ← hφ]; exact hab
    exact RingOfIntegers.ext (mul_right_cancel₀ (inv_ne_zero hd0) this)
  let KS : Submodule (𝓞 E) E :=
    { carrier := {x | IsInt (x * α) ∧ IsInt (x * α')}
      add_mem' := by
        rintro x y ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
        exact ⟨⟨a + b, by rw [add_mul, ← ha, ← hb]; simp⟩, ⟨a' + b', by rw [add_mul, ← ha', ← hb']; simp⟩⟩
      zero_mem' := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
      smul_mem' := by
        rintro c x ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
        exact ⟨⟨c * a, by rw [Algebra.smul_def, mul_assoc, ← ha]; simp⟩,
          ⟨c * a', by rw [Algebra.smul_def, mul_assoc, ← ha']; simp⟩⟩ }
  let A : Ideal (𝓞 E) := (cc : Submodule (𝓞 E) E).comap φ
  let B : Ideal (𝓞 E) := ((cc : Submodule (𝓞 E) E) ⊓ KS).comap φ
  have hA : ∀ a : 𝓞 E, a ∈ A ↔ (a : E) * (d : E)⁻¹ ∈ cc := fun a => by
    simp only [A, Submodule.mem_comap, hφ, FractionalIdeal.mem_coe]
  have hB : ∀ a : 𝓞 E, a ∈ B ↔ (a : E) * (d : E)⁻¹ ∈ cc ∧
      IsInt ((a : E) * (d : E)⁻¹ * α) ∧ IsInt ((a : E) * (d : E)⁻¹ * α') := fun a => by
    simp only [B, Submodule.mem_comap, hφ, Submodule.mem_inf, FractionalIdeal.mem_coe]; rfl
  have hlift : ∀ x ∈ cc, ∃ a : 𝓞 E, (a : E) * (d : E)⁻¹ = x := by
    intro x hx
    obtain ⟨a, ha⟩ := hden x hx
    refine ⟨a, ?_⟩
    have : (a : E) = (d : E) * x := by rw [Algebra.smul_def] at ha; exact ha
    rw [this]; field_simp
  have hBA : B ≤ A := fun a ha => (hA a).mpr ((hB a).mp ha).1
  have hmul : B = A * rr := by
    apply le_antisymm
    · obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hBA
      rw [hC]
      apply Ideal.mul_mono_right
      intro c hc
      rw [hrr]
      intro x hx
      obtain ⟨a, ha⟩ := hlift x hx
      have haA : a ∈ A := (hA a).mpr (by rw [ha]; exact hx)
      have : a * c ∈ B := by rw [hC]; exact Ideal.mul_mem_mul haA hc
      obtain ⟨_, h1, h2⟩ := (hB _).mp this
      constructor
      · convert h1 using 1; push_cast; rw [← ha]; ring
      · convert h2 using 1; push_cast; rw [← ha]; ring
    · rw [Ideal.mul_le]
      intro a ha c hc
      have hx := (hA a).mp ha
      obtain ⟨h1, h2⟩ := (hrr c).mp hc _ hx
      refine (hB _).mpr ⟨?_, ?_, ?_⟩
      · exact (hA _).mp (A.mul_mem_right c ha)
      · convert h1 using 1; push_cast; ring
      · convert h2 using 1; push_cast; ring
  have hAne : A ≠ ⊥ := by
    intro h
    apply hcc
    rw [FractionalIdeal.eq_zero_iff]
    intro x hx
    obtain ⟨a, ha⟩ := hlift x hx
    have haA : a ∈ A := (hA a).mpr (by rw [ha]; exact hx)
    rw [h, Ideal.mem_bot] at haA
    rw [← ha, haA]; simp
  have hHm : H = A.toAddSubgroup.map φ.toAddMonoidHom := by
    ext x
    rw [hH, AddSubgroup.mem_map]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hlift x hx
      exact ⟨a, (hA a).mpr (by rw [ha]; exact hx), by rw [← ha]; exact hφ a⟩
    · rintro ⟨a, ha, rfl⟩
      have := (hA a).mp ha
      rw [← hφ] at this; exact this
  have hKm : K ⊓ H = B.toAddSubgroup.map φ.toAddMonoidHom := by
    ext x
    rw [AddSubgroup.mem_inf, hH, hK, AddSubgroup.mem_map]
    constructor
    · rintro ⟨hk, hx⟩
      obtain ⟨a, ha⟩ := hlift x hx
      exact ⟨a, (hB a).mpr (by rw [ha]; exact ⟨hx, hk⟩), by rw [← ha]; exact hφ a⟩
    · rintro ⟨a, ha, rfl⟩
      have := (hB a).mp ha
      rw [← hφ] at this; exact ⟨this.2, this.1⟩
  rw [← AddSubgroup.inf_relIndex_right, hKm, hHm,
    AddSubgroup.relIndex_map_map_of_injective _ _ hφinj]
  have h1 := AddSubgroup.relIndex_mul_index (H := B.toAddSubgroup) (K := A.toAddSubgroup) hBA
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, hmul, map_mul, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hAne))
    (by rw [hmul]; exact h1)
end Formalism.HermitianLatticeCounting.P
