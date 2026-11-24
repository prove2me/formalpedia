-- Prove2me | solution 1 for Formalism.L2.Pj.LocalUnitReduction.mem_of_forall_sup_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:33.736438+00:00
-- url     : https://prove2.me/submissions/6a971124-5ebb-47c6-a60a-3ac2721cd3e5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_IsUnitMkOfForallPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocalUnitReduction
variable {K' Fr : Type*} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
  {ι : Type*} {R : ι → Type*} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
  (φ : ∀ c, Fr →ₐ[K'] R c)
namespace Formalism.L2.Pj.LocalUnitReduction
theorem _root_.solution [Fintype ι] (hinj : ∀ f : Fr, (∀ c, φ c f = 0) → f = 0)
    (hone : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q →
      RingHom.ker (φ c') ≤ Q → c = c')
    {f : Fr} (hf : ∀ c, f ∈ J ⊔ RingHom.ker (φ c)) : f ∈ J := by
  classical
  by_contra hfJ
  let C : Ideal Fr :=
    { carrier := {x | x * f ∈ J}
      add_mem' := fun {a b} ha hb => by simpa [add_mul] using J.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r x hx => by simpa [smul_eq_mul, mul_assoc] using J.mul_mem_left r hx }
  have hC : C ≠ ⊤ := fun h => by
    have h1 : (1 : Fr) ∈ C := h ▸ Submodule.mem_top
    exact hfJ (by simpa [C] using h1)
  obtain ⟨Q, hQ, hCQ⟩ := Ideal.exists_le_maximal C hC
  haveI := hQ.isPrime
  have hJQ : J ≤ Q := fun x hx => hCQ (show x * f ∈ J from J.mul_mem_right f hx)
  have h1Q : (1 : Fr) ∉ Q := fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
  have ht : ∀ c, ∃ t : Fr, (¬ RingHom.ker (φ c) ≤ Q → t ∈ RingHom.ker (φ c)) ∧ t ∉ Q := by
    intro c
    by_cases h : RingHom.ker (φ c) ≤ Q
    · exact ⟨1, fun h' => absurd h h', h1Q⟩
    · obtain ⟨t, htk, htQ⟩ := Set.not_subset.mp h
      exact ⟨t, fun _ => htk, htQ⟩
  choose t ht2 htQ using ht
  have hTQ : ∏ c, t c ∉ Q := fun h => by
    obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact htQ c hc
  have hTk : ∀ c, ¬ RingHom.ker (φ c) ≤ Q → φ c (∏ c, t c) = 0 := fun c hc => by
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) ((RingHom.mem_ker).mp (ht2 c hc))
  by_cases h0 : ∃ c0, RingHom.ker (φ c0) ≤ Q
  · obtain ⟨c0, hc0⟩ := h0
    obtain ⟨j, hj, k0, hk0, rfl⟩ := Submodule.mem_sup.mp (hf c0)
    have hTk0 : (∏ c, t c) * k0 = 0 := hinj _ fun c => by
      by_cases hc : c = c0
      · subst hc
        rw [map_mul, (RingHom.mem_ker).mp hk0, mul_zero]
      · have hcQ : ¬ RingHom.ker (φ c) ≤ Q := fun h => hc (hone Q hQ.isPrime hJQ c c0 h hc0)
        rw [map_mul, hTk c hcQ, zero_mul]
    apply hTQ
    apply hCQ
    show (∏ c, t c) * (j + k0) ∈ J
    rw [mul_add, hTk0, add_zero]
    exact J.mul_mem_left _ hj
  · push_neg at h0
    have hT0 : ∏ c, t c = 0 := hinj _ fun c => hTk c (h0 c)
    exact hTQ (hT0 ▸ Q.zero_mem)
end Formalism.L2.Pj.LocalUnitReduction
