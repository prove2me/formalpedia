-- Prove2me | solution 1 for Formalism.L2.G.precomplete_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:32.214218+00:00
-- url     : https://prove2.me/submissions/a64fec18-28e2-43cd-9aa3-fe73d19aff88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution {R : Type*} [CommRing R] (π : R) [IsPrecomplete (Ideal.span {π}) R] (d : ℕ) :
    IsPrecomplete (Ideal.span {π}) (Fin d → R) := by
  have key : ∀ (m : ℕ) (v : Fin d → R),
      v ∈ (Ideal.span {π} ^ m • ⊤ : Submodule R (Fin d → R)) ↔ ∀ i, v i ∈ Ideal.span {π} ^ m := by
    intro m v
    constructor
    · intro hv
      refine Submodule.smul_induction_on (p := fun v : Fin d → R => ∀ i, v i ∈ Ideal.span {π} ^ m)
        hv ?_ ?_
      · intro r hr w _ i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy i
        simp only [Pi.add_apply]
        exact Ideal.add_mem _ (hx i) (hy i)
    · intro hv
      have hsum : v = ∑ i, v i • Pi.single i (1 : R) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hv i) Submodule.mem_top
  have key1 : ∀ (m : ℕ) (r : R), r ∈ (Ideal.span {π} ^ m • ⊤ : Submodule R R) ↔
      r ∈ Ideal.span {π} ^ m := by
    intro m r
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hcomp : ∀ i, ∃ L : R, ∀ k,
      f k i ≡ L [SMOD (Ideal.span {π} ^ k • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec inferInstance (fun {a b} hab => ?_)
    have h1 := hf hab
    rw [SModEq.sub_mem] at h1 ⊢
    rw [key] at h1
    rw [key1]
    simpa using h1 i
  choose L hL using hcomp
  refine ⟨L, fun k => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  have h2 := hL i k
  rw [SModEq.sub_mem, key1] at h2
  simpa using h2
end Formalism.L2.G
