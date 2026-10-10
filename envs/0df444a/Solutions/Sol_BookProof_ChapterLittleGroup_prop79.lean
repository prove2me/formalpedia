-- Prove2me | solution 1 for BookProof.ChapterLittleGroup.prop79
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:39:07.193734+00:00
-- url     : https://prove2.me/submissions/35803384-4b86-430f-9f1c-c97ab2e11f3e

-- Generated from ChapterLittleGroup.lean — solution of BookProof.ChapterLittleGroup.prop79
import Mathlib
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterLittleGroup




variable {G : Type*} [Group G] {K : Type*}

variable {G : Type*} [Group G] {K : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (q : K → G) (hq : Function.Injective q) (l₀ : K)
    (α : K → G) (Λ : G → K → K)
    (hα : ∀ k, α k * q l₀ * (α k)⁻¹ = q k)
    (hΛ : ∀ (S : G) (k : K), S * q k * S⁻¹ = q (Λ S k))
    (k : K) :
    Hset α Λ k = (littleGroup q l₀ : Set G) := by

  -- Let's take an element g from Hset α Λ k. By definition, there exists some S such that g = (α (Λ
  -- S k))⁻¹ * S * α k.
  apply Set.eq_of_subset_of_subset;
  · intro g hg
    obtain ⟨S, rfl⟩ := hg
    have h_comm : ((α (Λ S k))⁻¹ * S * α k) * q l₀ = q l₀ * ((α (Λ S k))⁻¹ * S * α k) := by
      have h_comm : S * α k * q l₀ = q (Λ S k) * S * α k := by
        simp [ ← hΛ, mul_assoc ];
        simpa [ mul_assoc ] using eq_mul_inv_of_mul_eq ( hα k );
      have := hα ( Λ S k );
      simp [ ← this, mul_assoc, h_comm ]
    generalize_proofs at *;
    exact fun x hx => by aesop;
  · intro g hg
    use α k * g * (α k)⁻¹;
    simp_all only [mul_assoc, littleGroup, SetLike.mem_coe, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq, inv_mul_cancel, mul_one];
    simp_all only [hq.eq_iff, ← mul_assoc, right_eq_mul];
    have hΛ_eq : Λ (α k * g * (α k)⁻¹) k = k := by
      have h_comm : (α k * g * (α k)⁻¹) * (α k * q l₀ * (α k)⁻¹) * (α k * g * (α k)⁻¹)⁻¹ = α k * q
          l₀ * (α k)⁻¹ := by
        simp [ mul_assoc ];
        simp [ ← mul_assoc, ← hg ];
      grind;
    rw [ hΛ_eq, inv_mul_cancel ]
