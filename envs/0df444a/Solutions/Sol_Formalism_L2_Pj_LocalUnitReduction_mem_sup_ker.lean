-- Prove2me | solution 1 for Formalism.L2.Pj.LocalUnitReduction.mem_sup_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:34.081441+00:00
-- url     : https://prove2.me/submissions/72f2091f-6889-4ea7-9de4-ab021f52e50e

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
theorem _root_.solution {c : ι}
    (hloc : ∀ r : R c, ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    {f : Fr} (hf : φ c f ∈ Ideal.map (φ c) J) : f ∈ J ⊔ RingHom.ker (φ c) := by
  have key : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q →
      ∀ y ∈ Ideal.map (φ c) J, ∃ s g : Fr, s ∉ Q ∧ g ∈ J ∧ φ c s * y = φ c g := by
    intro Q hQ hJQ hkQ y hy
    have h1Q : (1 : Fr) ∉ Q := fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
    have hy' : y ∈ Submodule.span (R c) (φ c '' J) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨1, j, h1Q, hj, by simp⟩
    | zero => exact ⟨1, 0, h1Q, J.zero_mem, by simp⟩
    | add y1 y2 _ _ ih1 ih2 =>
      obtain ⟨s1, g1, hs1, hg1, e1⟩ := ih1
      obtain ⟨s2, g2, hs2, hg2, e2⟩ := ih2
      refine ⟨s1 * s2, s2 * g1 + s1 * g2, fun h => (hQ.mem_or_mem h).elim hs1 hs2,
        J.add_mem (J.mul_mem_left _ hg1) (J.mul_mem_left _ hg2), ?_⟩
      rw [map_mul, map_add, map_mul, map_mul, ← e1, ← e2]
      ring
    | smul r y _ ih =>
      obtain ⟨s, g, hs, hg, e⟩ := ih
      obtain ⟨a, p, hp, ep⟩ := hloc r
      refine ⟨p * s, a * g, fun h => (hQ.mem_or_mem h).elim (hp Q hQ hJQ hkQ) hs,
        J.mul_mem_left _ hg, ?_⟩
      rw [smul_eq_mul, map_mul, map_mul, ← e, ← ep]
      ring
  by_contra hfL
  let C : Ideal Fr :=
    { carrier := {x | x * f ∈ J ⊔ RingHom.ker (φ c)}
      add_mem' := fun {a b} ha hb => by
        simpa [add_mul] using (J ⊔ RingHom.ker (φ c)).add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        simpa [smul_eq_mul, mul_assoc] using (J ⊔ RingHom.ker (φ c)).mul_mem_left r hx }
  have hC : C ≠ ⊤ := fun h => by
    have h1 : (1 : Fr) ∈ C := h ▸ Submodule.mem_top
    exact hfL (by simpa [C] using h1)
  obtain ⟨Q, hQ, hCQ⟩ := Ideal.exists_le_maximal C hC
  have hLC : J ⊔ RingHom.ker (φ c) ≤ C := fun x hx =>
    (show x * f ∈ J ⊔ RingHom.ker (φ c) from (J ⊔ RingHom.ker (φ c)).mul_mem_right f hx)
  have hLQ := hLC.trans hCQ
  obtain ⟨s, g, hs, hg, e⟩ :=
    key Q hQ.isPrime (le_sup_left.trans hLQ) (le_sup_right.trans hLQ) (φ c f) hf
  apply hs
  apply hCQ
  show s * f ∈ J ⊔ RingHom.ker (φ c)
  have hk : s * f - g ∈ RingHom.ker (φ c) := by
    rw [RingHom.mem_ker, map_sub, map_mul, e, sub_self]
  have hsum := (J ⊔ RingHom.ker (φ c)).add_mem (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hk)
  simpa using hsum
end Formalism.L2.Pj.LocalUnitReduction
